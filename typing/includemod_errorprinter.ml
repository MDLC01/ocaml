(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Florian Angeletti, projet Cambium, Inria Paris             *)
(*                                                                        *)
(*   Copyright 2021 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

module Style = Misc.Style

module Context = struct
  type pos =
    | Module of Ident.t
    | Modtype of Ident.t
    | Arg of Types.functor_parameter
    | Body of Types.functor_parameter

  let path_of_context = function
      Module id :: rem ->
        let rec subm path = function
          | [] -> path
          | Module id :: rem -> subm (Path.Pdot (path, Ident.name id)) rem
          | _ -> assert false
        in subm (Path.Pident id) rem
    | _ -> assert false


  let rec context ppf = function
      Module id :: rem ->
        Format.fprintf ppf "@[<2>module %a%a@]" Printtyp.ident id args rem
    | Modtype id :: rem ->
        Format.fprintf ppf "@[<2>module type %a =@ %a@]"
          Printtyp.ident id context_mty rem
    | Body x :: rem ->
        Format.fprintf ppf "functor (%s) ->@ %a" (argname x) context_mty rem
    | Arg x :: rem ->
        Format.fprintf ppf "functor (%s : %a) -> ..."
          (argname x) context_mty rem
    | [] ->
        Format.fprintf ppf "<here>"
  and context_mty ppf = function
      (Module _ | Modtype _) :: _ as rem ->
        Format.fprintf ppf "@[<2>sig@ %a@;<1 -2>end@]" context rem
    | cxt -> context ppf cxt
  and args ppf = function
      Body x :: rem ->
        Format.fprintf ppf "(%s)%a" (argname x) args rem
    | Arg x :: rem ->
        Format.fprintf ppf "(%s :@ %a) : ..." (argname  x) context_mty rem
    | cxt ->
        Format.fprintf ppf " :@ %a" context_mty cxt
  and argname = function
    | Types.Unit -> ""
    | Types.Named (None, _) -> "_"
    | Types.Named (Some id, _) -> Ident.name id

  let alt_pp ppf cxt =
    if cxt = [] then () else
    if List.for_all (function Module _ -> true | _ -> false) cxt then
      Format.fprintf ppf "in module %a,"
        (Style.as_inline_code Printtyp.path) (path_of_context cxt)
    else
      Format.fprintf ppf "@[<hv 2>at position@ %a,@]"
        (Style.as_inline_code context) cxt

  let pp ppf cxt =
    if cxt = [] then () else
    if List.for_all (function Module _ -> true | _ -> false) cxt then
      Format.fprintf ppf "In module %a:@ "
        (Style.as_inline_code Printtyp.path) (path_of_context cxt)
    else
      Format.fprintf ppf "@[<hv 2>At position@ %a@]@ "
        (Style.as_inline_code context) cxt
end

module Illegal_permutation = struct
  (** Extraction of information in case of illegal permutation
      in a module type *)

  (** When examining coercions, we only have runtime component indices,
      we use thus a limited version of {!pos}. *)
  type coerce_pos =
    | Item of int
    | InArg
    | InBody

  let either f x g y = match f x with
    | None -> g y
    | Some _ as v -> v

  (** We extract a lone transposition from a full tree of permutations. *)
  let rec transposition_under path (coerc:Typedtree.module_coercion) =
    match coerc with
    | Tcoerce_structure(c,_) ->
        either
          (not_fixpoint path 0) c
          (first_non_id path 0) c
    | Tcoerce_functor(arg,res) ->
        either
          (transposition_under (InArg::path)) arg
          (transposition_under (InBody::path)) res
    | Tcoerce_none -> None
    | Tcoerce_alias _ | Tcoerce_primitive _ ->
        (* these coercions are not inversible, and raise an error earlier when
           checking for module type equivalence *)
        assert false
  (* we search the first point which is not invariant at the current level *)
  and not_fixpoint path pos = function
    | [] -> None
    | (n, _) :: q ->
        if n = pos then
          not_fixpoint path (pos+1) q
        else
          Some(List.rev path, pos, n)
  (* we search the first item with a non-identity inner coercion *)
  and first_non_id path pos = function
    | [] -> None
    | (_, Typedtree.Tcoerce_none) :: q -> first_non_id path (pos + 1) q
    | (_,c) :: q ->
        either
          (transposition_under (Item pos :: path)) c
          (first_non_id path (pos + 1)) q

  let transposition c =
    match transposition_under [] c with
    | None -> raise Not_found
    | Some x -> x

  let rec runtime_item k = function
    | [] -> raise Not_found
    | item :: q ->
        if not(Includemod.is_runtime_component item) then
          runtime_item k q
        else if k = 0 then
          item
        else
          runtime_item (k-1) q

  (* Find module type at position [path] and convert the [coerce_pos] path to
     a [pos] path *)
  let rec find env ctx path (mt:Types.module_type) = match mt, path with
    | (Mty_ident p | Mty_alias p), _ ->
        begin match (Env.find_modtype p env).mtd_type with
        | None -> raise Not_found
        | Some mt -> find env ctx path mt
        end
    | Mty_signature s , [] -> List.rev ctx, s
    | Mty_signature s, Item k :: q ->
        begin match runtime_item k s with
        | Sig_module (id, _, md,_,_) ->
            find env (Context.Module id :: ctx) q md.md_type
        | _ -> raise Not_found
        end
    | Mty_functor(Named (_,mt) as arg,_), InArg :: q ->
        find env (Context.Arg arg :: ctx) q mt
    | Mty_functor(arg, mt), InBody :: q ->
        find env (Context.Body arg :: ctx) q mt
    | _ -> raise Not_found

  let find env path mt = find env [] path mt
  let item mt k = Includemod.item_ident_name (runtime_item k mt)

  let pp_item ppf (id,_,kind) =
    Format.fprintf ppf "%s %a"
      (Includemod.kind_of_field_desc kind)
      Style.inline_code (Ident.name id)

  let pp ctx_printer env ppf (mty,c) =
    try
      let p, k, l = transposition c in
      let ctx, mt = find env p mty in
      Format.fprintf ppf
        "@[<hv 2>Illegal permutation of runtime components in a module type.@ \
         @[For example,@ %a@]@ @[the %a@ and the %a are not in the same order@ \
         in the expected and actual module types.@]@]"
        ctx_printer ctx pp_item (item mt k) pp_item (item mt l)
    with Not_found -> (* this should not happen *)
      Format.fprintf ppf
        "Illegal permutation of runtime components in a module type."

end



module Err = Includemod.Error

let buffer = ref Bytes.empty
let is_big obj =
  let size = !Clflags.error_size in
  size > 0 &&
  begin
    if Bytes.length !buffer < size then buffer := Bytes.create size;
    try ignore (Marshal.to_buffer !buffer 0 size obj []); false
    with _ -> true
  end

let show_loc msg ppf loc =
  let pos = loc.Location.loc_start in
  if List.mem pos.Lexing.pos_fname [""; "_none_"; "//toplevel//"] then ()
  else Format.fprintf ppf "@\n@[<2>%a:@ %s@]" Location.print_loc loc msg

let show_locs ppf (loc1, loc2) =
  show_loc "Expected declaration" ppf loc2;
  show_loc "Actual declaration" ppf loc1


let dmodtype mty =
  let tmty = Printtyp.tree_of_modtype mty in
  Format.dprintf "%a" !Oprint.out_module_type tmty

let space ppf () = Format.fprintf ppf "@ "

(**
   In order to display a list of functor arguments in a compact format,
   we introduce a notion of shorthand for functor arguments.
   The aim is to first present the lists of actual and expected types with
   shorthands:

     (X: $S1) (Y: $S2) (Z: An_existing_module_type) ...
   does not match
     (X: $T1) (Y: A_real_path) (Z: $T3) ...

   and delay the full display of the module types corresponding to $S1, $S2,
   $T1, and $T3 to the suberror message.

*)
module With_shorthand = struct

  (** A item with a potential shorthand name *)
  type 'a named = {
    item: 'a;
    name : string;
  }

  type 'a t =
    | Original of 'a (** The shorthand has been discarded *)
    | Synthetic of 'a named
    (** The shorthand is potentially useful *)

  type functor_param =
    | Unit
    | Named of (Ident.t option * Types.module_type t)

  (** Shorthand generation *)
  type kind =
    | Got
    | Expected
    | Unneeded

  type variant =
    | App
    | Inclusion

  let elide_if_app ctx s = match ctx with
    | App -> Unneeded
    | Inclusion -> s

  let make side pos =
    match side with
    | Got -> Format.sprintf "$S%d" pos
    | Expected -> Format.sprintf "$T%d" pos
    | Unneeded -> "..."

  (** Add shorthands to a patch *)
  open Diffing
  let patch ctx p =
    let add_shorthand side pos mty =
      {name = (make side pos); item = mty }
    in
    let aux i d =
      let pos = i + 1 in
      let d = match d with
        | Insert mty ->
            Insert (add_shorthand Expected pos mty)
        | Delete mty ->
            Delete (add_shorthand (elide_if_app ctx Got) pos mty)
        | Change (g, e, p) ->
            Change
              (add_shorthand Got pos g,
               add_shorthand Expected pos e, p)
        | Keep (g, e, p) ->
            Keep (add_shorthand Got pos g,
                          add_shorthand (elide_if_app ctx Expected) pos e, p)
      in
      pos, d
    in
    List.mapi aux p

  (** Shorthand computation from named item *)
  let modtype (r : _ named) = match r.item with
    | Types.Mty_ident _
    | Types.Mty_alias _
    | Types.Mty_signature []
      -> Original r.item
    | Types.Mty_signature _ | Types.Mty_functor _
      -> Synthetic r

  let functor_param (ua : _ named) = match ua.item with
    | Types.Unit -> Unit
    | Types.Named (from, mty) ->
        Named (from, modtype { ua with item = mty })

  (** Printing of arguments with shorthands *)
  let pp ppx = function
    | Original x -> ppx x
    | Synthetic s -> Format.dprintf "%s" s.name

  let pp_orig ppx = function
    | Original x | Synthetic { item=x; _ } -> ppx x

  let definition x = match functor_param x with
    | Unit -> Format.dprintf "()"
    | Named(_,short_mty) ->
        match short_mty with
        | Original mty -> dmodtype mty
        | Synthetic {name; item = mty} ->
            Format.dprintf
              "%s@ =@ %t" name (dmodtype mty)

  let param x = match functor_param x with
    | Unit -> Format.dprintf "()"
    | Named (_, short_mty) ->
        pp dmodtype short_mty

  let qualified_param x = match functor_param x with
    | Unit -> Format.dprintf "()"
    | Named (None, Original (Mty_signature []) ) ->
        Format.dprintf "(sig end)"
    | Named (None, short_mty) ->
        pp dmodtype short_mty
    | Named (Some p, short_mty) ->
        Format.dprintf "(%s : %t)"
          (Ident.name p) (pp dmodtype short_mty)

  let definition_of_argument ua =
    let arg, mty = ua.item in
    match (arg: Err.functor_arg_descr) with
    | Unit -> Format.dprintf "()"
    | Empty_struct -> Format.dprintf "(struct end)"
    | Named p ->
        let mty = modtype { ua with item = mty } in
        Format.dprintf
          "%a@ :@ %t"
          Printtyp.path p
          (pp_orig dmodtype mty)
    | Anonymous ->
        let short_mty = modtype { ua with item = mty } in
        begin match short_mty with
        | Original mty -> dmodtype mty
        | Synthetic {name; item=mty} ->
            Format.dprintf "%s@ :@ %t" name (dmodtype mty)
        end

  let arg ua =
    let arg, mty = ua.item in
    match (arg: Err.functor_arg_descr) with
    | Unit -> Format.dprintf "()"
    | Empty_struct -> Format.dprintf "(struct end)"
    | Named p -> fun ppf -> Printtyp.path ppf p
    | Anonymous ->
        let short_mty = modtype { ua with item=mty } in
        pp dmodtype short_mty

end


module Functor_suberror = struct
  open Err

  let param_id x = match x.With_shorthand.item with
    | Types.Named (Some _ as x,_) -> x
    | Types.(Unit | Named(None,_)) -> None

  (** Print the list of params with style *)
  let pretty_params sep proj printer patch =
    let elt (x,param) =
      let sty = Diffing.(style @@ classify x) in
      Format.dprintf "%a%t%a"
        Format.pp_open_stag (Style.Style sty)
        (printer param)
        Format.pp_close_stag ()
    in
    let params = List.filter_map proj @@ List.map snd patch in
    Printtyp.functor_parameters ~sep elt params

  let expected d =
    let extract: _ Diffing.change -> _ = function
      | Insert mty
      | Keep(_,mty,_)
      | Change (_,mty,_) as x ->
          Some (param_id mty,(x, mty))
      | Delete _ -> None
    in
    pretty_params space extract With_shorthand.qualified_param d

  let drop_inserted_suffix patch =
    let rec drop = function
      | Diffing.Insert _ :: q -> drop q
      | rest -> List.rev rest in
    drop (List.rev patch)

  let prepare_patch ~drop ~ctx patch =
    let drop_suffix x = if drop then drop_inserted_suffix x else x in
    patch |> drop_suffix |> With_shorthand.patch ctx


  module Inclusion = struct

    let got d =
      let extract: _ Diffing.change -> _ = function
      | Delete mty
      | Keep (mty,_,_)
      | Change (mty,_,_) as x ->
          Some (param_id mty,(x,mty))
      | Insert _ -> None
      in
      pretty_params space extract With_shorthand.qualified_param d

    let insert mty =
      Format.dprintf
        "An argument appears to be missing with module type@;<1 2>@[%t@]"
        (With_shorthand.definition mty)

    let delete mty =
      Format.dprintf
        "An extra argument is provided of module type@;<1 2>@[%t@]"
        (With_shorthand.definition mty)

      let ok x y =
        Format.dprintf
          "Module types %t and %t match"
          (With_shorthand.param x)
          (With_shorthand.param y)

      let diff g e more =
        let g = With_shorthand.definition g in
        let e = With_shorthand.definition e in
        Format.dprintf
          "Module types do not match:@ @[%t@]@;<1 -2>does not include@ \
           @[%t@]%t"
          g e (more ())

      let incompatible = function
        | Types.Unit ->
            Format.dprintf
              "The functor was expected to be applicative at this position"
        | Types.Named _ ->
            Format.dprintf
              "The functor was expected to be generative at this position"

      let patch env got expected =
        Includemod.Functor_inclusion_diff.diff env got expected
        |> prepare_patch ~drop:false ~ctx:Inclusion

    end

  module App = struct

    let patch env ~f ~args =
      Includemod.Functor_app_diff.diff env ~f ~args
      |> prepare_patch ~drop:true ~ctx:App

    let got d =
      let extract: _ Diffing.change -> _ = function
        | Delete mty
        | Keep (mty,_,_)
        | Change (mty,_,_) as x ->
            Some (None,(x,mty))
        | Insert _ -> None
      in
      pretty_params space extract With_shorthand.arg d

    let delete mty =
      Format.dprintf
        "The following extra argument is provided@;<1 2>@[%t@]"
        (With_shorthand.definition_of_argument mty)

    let insert = Inclusion.insert

    let ok x y =
      let pp_orig_name = match With_shorthand.functor_param y with
        | With_shorthand.Named (_, Original mty) ->
            Format.dprintf " %t" (dmodtype mty)
        | _ -> ignore
      in
      Format.dprintf
        "Module %t matches the expected module type%t"
        (With_shorthand.arg x)
        pp_orig_name

    let diff g e more =
      let g = With_shorthand.definition_of_argument g in
      let e = With_shorthand.definition e in
      Format.dprintf
        "Modules do not match:@ @[%t@]@;<1 -2>\
         is not included in@ @[%t@]%t"
        g e (more ())

    (** Specialized to avoid introducing shorthand names
        for single change difference
    *)
    let single_diff g e more =
      let _arg, mty = g.With_shorthand.item in
      let e = match e.With_shorthand.item with
        | Types.Unit -> Format.dprintf "()"
        | Types.Named(_, mty) -> dmodtype mty
      in
      Format.dprintf
        "Modules do not match:@ @[%t@]@;<1 -2>\
         is not included in@ @[%t@]%t"
        (dmodtype mty) e (more ())


    let incompatible = function
      | Unit ->
          Format.dprintf
            "The functor was expected to be applicative at this position"
      | Named _ | Anonymous ->
          Format.dprintf
            "The functor was expected to be generative at this position"
      | Empty_struct ->
          (* an empty structure can be used in both applicative and generative
             context *)
          assert false
  end

  let subcase sub ~expansion_token env (pos, diff) =
    Location.msg "%a%a%a%a@[<hv 2>%t@]%a"
      Format.pp_print_tab ()
      Format.pp_open_tbox ()
      Diffing.prefix (pos, Diffing.classify diff)
      Format.pp_set_tab ()
      (Printtyp.wrap_printing_env env ~error:true
         (fun () -> sub ~expansion_token env diff)
      )
     Format.pp_close_tbox ()

  let onlycase sub ~expansion_token env (_, diff) =
    Location.msg "%a@[<hv 2>%t@]"
      Format.pp_print_tab ()
      (Printtyp.wrap_printing_env env ~error:true
         (fun () -> sub ~expansion_token env diff)
      )

  let params sub ~expansion_token env l =
    let rec aux subcases = function
      | [] -> subcases
      | (_, Diffing.Keep _) as a :: q ->
          aux (subcase sub ~expansion_token env a :: subcases) q
      | a :: q ->
          List.fold_left (fun acc x ->
            (subcase sub ~expansion_token:false env x) :: acc
            )
            (subcase sub ~expansion_token env a :: subcases)
            q
    in
    match l with
    | [a] -> [onlycase sub ~expansion_token env a]
    | l -> aux [] l
end


(** Construct a linear presentation of the error tree *)

open Err

(* Context helper functions *)
let with_context ?loc ctx printer diff =
  Location.msg ?loc "%a%a" Context.pp (List.rev ctx)
    printer diff

let dwith_context ?loc ctx printer =
  Location.msg ?loc "%a%t" Context.pp (List.rev ctx) printer

let dwith_context_and_elision ?loc ctx printer diff =
  if is_big (diff.got,diff.expected) then
    Location.msg ?loc "..."
  else
    dwith_context ?loc ctx (printer diff)

(* Merge sub msgs into one printer *)
let coalesce msgs =
  match List.rev msgs with
  | [] -> ignore
  | before ->
      let ctx ppf =
        Format.pp_print_list ~pp_sep:space
          (fun ppf x -> x.Location.txt ppf)
          ppf before in
      ctx

let subcase_list l ppf = match l with
  | [] -> ()
  | _ :: _ ->
      Format.fprintf ppf "@;<1 -2>@[%a@]"
        (Format.pp_print_list ~pp_sep:space
           (fun ppf f -> f.Location.txt ppf)
        )
        (List.rev l)

(* Printers for leaves *)
let core env id x =
  match x with
  | Err.Value_descriptions diff ->
      Format.dprintf "@[<v>@[<hv>%s:@;<1 2>%a@ %s@;<1 2>%a@]%a%a%t@]"
        "Values do not match"
        !Oprint.out_sig_item
        (Printtyp.tree_of_value_description id diff.got)
        "is not included in"
        !Oprint.out_sig_item
        (Printtyp.tree_of_value_description id diff.expected)
        (Includecore.report_value_mismatch
           "the first" "the second" env) diff.symptom
        show_locs (diff.got.val_loc, diff.expected.val_loc)
        Printtyp.Conflicts.print_explanations
  | Err.Type_declarations diff ->
      Format.dprintf "@[<v>@[<hv>%s:@;<1 2>%a@ %s@;<1 2>%a@]%a%a%t@]"
        "Type declarations do not match"
        !Oprint.out_sig_item
        (Printtyp.tree_of_type_declaration id diff.got Trec_first)
        "is not included in"
        !Oprint.out_sig_item
        (Printtyp.tree_of_type_declaration id diff.expected Trec_first)
        (Includecore.report_type_mismatch
           "the first" "the second" "declaration" env) diff.symptom
        show_locs (diff.got.type_loc, diff.expected.type_loc)
        Printtyp.Conflicts.print_explanations
  | Err.Extension_constructors diff ->
      Format.dprintf "@[<v>@[<hv>%s:@;<1 2>%a@ %s@;<1 2>%a@]@ %a%a%t@]"
        "Extension declarations do not match"
        !Oprint.out_sig_item
        (Printtyp.tree_of_extension_constructor id diff.got Text_first)
        "is not included in"
        !Oprint.out_sig_item
        (Printtyp.tree_of_extension_constructor id diff.expected Text_first)
        (Includecore.report_extension_constructor_mismatch
           "the first" "the second" "declaration" env) diff.symptom
        show_locs (diff.got.ext_loc, diff.expected.ext_loc)
        Printtyp.Conflicts.print_explanations
  | Err.Class_type_declarations diff ->
      Format.dprintf
        "@[<hv 2>Class type declarations do not match:@ \
         %a@;<1 -2>does not match@ %a@]@ %a%t"
        !Oprint.out_sig_item
        (Printtyp.tree_of_cltype_declaration id diff.got Trec_first)
        !Oprint.out_sig_item
        (Printtyp.tree_of_cltype_declaration id diff.expected Trec_first)
        (Includeclass.report_error Type_scheme) diff.symptom
        Printtyp.Conflicts.print_explanations
  | Err.Class_declarations {got;expected;symptom} ->
      let t1 = Printtyp.tree_of_class_declaration id got Trec_first in
      let t2 = Printtyp.tree_of_class_declaration id expected Trec_first in
      Format.dprintf
        "@[<hv 2>Class declarations do not match:@ \
         %a@;<1 -2>does not match@ %a@]@ %a%t"
        !Oprint.out_sig_item t1
        !Oprint.out_sig_item t2
        (Includeclass.report_error Type_scheme) symptom
        Printtyp.Conflicts.print_explanations

let suggest_adding_field ppf item =
  let id, _, kind = Includemod.item_ident_name item in
  Format.fprintf ppf "Try adding a %s %a"
    (Includemod.kind_of_field_desc kind)
    Style.inline_code (Ident.name id)

let suggest_renaming_field ppf (item, suggested_name) =
  let current_id, _, kind = Includemod.item_ident_name item in
  Format.fprintf ppf "Try renaming %s %a to %a"
    (Includemod.kind_of_field_desc kind)
    Style.inline_code (Ident.name current_id)
    Style.inline_code suggested_name

let suggest_changing_value_type ppf (id, suggested_type) =
  Format.fprintf ppf "Try changing value %a to be a %a"
    Style.inline_code (Ident.name id)
    (Style.as_inline_code Printtyp.type_expr) suggested_type

let module_types {Err.got=mty1; expected=mty2} =
  Format.dprintf
    "@[<hv 2>Modules do not match:@ \
     %a@;<1 -2>is not included in@ %a@]"
    !Oprint.out_module_type (Printtyp.tree_of_modtype mty1)
    !Oprint.out_module_type (Printtyp.tree_of_modtype mty2)

let eq_module_types {Err.got=mty1; expected=mty2} =
  Format.dprintf
    "@[<hv 2>Module types do not match:@ \
     %a@;<1 -2>is not equal to@ %a@]"
    !Oprint.out_module_type (Printtyp.tree_of_modtype mty1)
    !Oprint.out_module_type (Printtyp.tree_of_modtype mty2)

let module_type_declarations id {Err.got=d1 ; expected=d2} =
  Format.dprintf
    "@[<hv 2>Module type declarations do not match:@ \
     %a@;<1 -2>does not match@ %a@]"
    !Oprint.out_sig_item (Printtyp.tree_of_modtype_declaration id d1)
    !Oprint.out_sig_item (Printtyp.tree_of_modtype_declaration id d2)

let interface_mismatch ppf (diff: _ Err.diff) =
  Format.fprintf ppf
    "The implementation %a@ does not match the interface %a:@ "
    Style.inline_code diff.got Style.inline_code diff.expected

let core_module_type_symptom (x:Err.core_module_type_symptom)  =
  match x with
  | Not_an_alias | Not_an_identifier | Abstract_module_type
  | Incompatible_aliases ->
      if Printtyp.Conflicts.exists () then
        Some Printtyp.Conflicts.print_explanations
      else None
  | Unbound_module_path path ->
      Some(Format.dprintf "Unbound module %a"
             (Style.as_inline_code Printtyp.path) path
          )

(* Construct a linearized error message from the error tree *)

let rec module_type ~expansion_token ~eqmode ~env ~before ~ctx diff =
  match diff.symptom with
  | Invalid_module_alias _ (* the difference is non-informative here *)
  | After_alias_expansion _ (* we print only the expanded module types *) ->
      module_type_symptom ~eqmode ~expansion_token ~env ~before ~ctx
        diff.symptom
  | Functor Params d -> (* We jump directly to the functor param error *)
      functor_params ~expansion_token ~env ~before ~ctx d
  | _ ->
      let inner = if eqmode then eq_module_types else module_types in
      let next =
        match diff.symptom with
        | Mt_core _ ->
            (* In those cases, the refined error messages for the current error
               will at most add some minor comments on the current error.
               It is thus better to avoid eliding the current error message.
            *)
            dwith_context ctx (inner diff)
        | _ -> dwith_context_and_elision ctx inner diff
      in
      let before = next :: before in
      module_type_symptom ~eqmode ~expansion_token ~env ~before ~ctx
        diff.symptom

and module_type_symptom ~eqmode ~expansion_token ~env ~before ~ctx = function
  | Mt_core core ->
      begin match core_module_type_symptom core with
      | None -> before
      | Some msg -> Location.msg "%t" msg :: before
      end
  | Signature s -> signature ~expansion_token ~env ~before ~ctx s
  | Functor f -> functor_symptom ~expansion_token ~env ~before ~ctx f
  | After_alias_expansion diff ->
      module_type ~eqmode ~expansion_token ~env ~before ~ctx diff
  | Invalid_module_alias path ->
      let printer =
        Format.dprintf "Module %a cannot be aliased"
          (Style.as_inline_code Printtyp.path) path
      in
      dwith_context ctx printer :: before

and functor_params ~expansion_token ~env ~before ~ctx {got;expected;_} =
  let d = Functor_suberror.Inclusion.patch env got expected in
  let actual = Functor_suberror.Inclusion.got d in
  let expected = Functor_suberror.expected d in
  let main =
    Format.dprintf
      "@[<hv 2>Modules do not match:@ \
       @[functor@ %t@ -> ...@]@;<1 -2>is not included in@ \
       @[functor@ %t@ -> ...@]@]"
      actual expected
  in
  let msgs = dwith_context ctx main :: before in
  let functor_suberrors =
    if expansion_token then
      Functor_suberror.params functor_arg_diff ~expansion_token env d
    else []
  in
  functor_suberrors @ msgs

and functor_symptom ~expansion_token ~env ~before ~ctx = function
  | Result res ->
      module_type ~expansion_token ~eqmode:false ~env ~before ~ctx res
  | Params d -> functor_params ~expansion_token ~env ~before ~ctx d

and signature ~expansion_token ~env ~before ~ctx sgs =
  let open struct
    type ('v, 't) field = {
      item : Types.signature_item;
      value : 'v;
      type_ : 't;
    }

    let field_name field = Ident.name (Types.signature_item_id field.item)

    type ('v, 't) suggestions = {
      add: ('v, 't) field list;
      rename: (('v, 't) field * string) list;
    }
  end in

  let fuzzy_match_names compatibility_test missings additions =
    let cutoff = 8 in
    let m = List.length missings in
    let n = List.length additions in

    (* An implementation of the Gale-Shapley algorithm, where missing fields
       propose and added fields accept or refuse. *)
    let stable_marriages () =
      let missing_fields = Array.of_list missings in
      let added_fields = Array.of_list additions in

      let preferences =
        let added_names =
          additions
          |> List.mapi (fun j field -> (field_name field, j))
          |> Misc.Trie.of_list
        in
        Array.init m (fun i ->
            let missing_name = field_name missing_fields.(i) in
            Misc.Trie.compute_preferences ~cutoff added_names missing_name)
      in
      (* [is_married.(i)] indicates whether there exists a [j] such that
         [missing_fields.(i)] and [added_fields.(j)] are married. *)
      let is_married = Array.make m false in
      (* [added_fields.(j)] is married with [missing_fields.(i)] iff
         [added_fields.(j) = Some (i, d)] where [d] is the edition distance
         between the names. *)
      let marriages = Array.make n None in

      (* Marries [missing_fields.(i)] with [added_fields.(j)], unless
         [added_fields.(j)] already has a better marriage. *)
      let try_marry i j d =
        if compatibility_test missing_fields.(i) added_fields.(j) then
          match marriages.(j) with
          | None ->
              marriages.(j) <- Some (i, d);
              is_married.(i) <- true
          | Some (i', d') ->
              if d < d' then (
                marriages.(j) <- Some (i, d);
                is_married.(i) <- true;
                is_married.(i') <- false)
      in

      let ok = ref false in
      while not !ok do
        ok := true;
        for i = 0 to m - 1 do
          if not is_married.(i) then
            match preferences.(i) () with
            | Seq.Nil -> ()
            | Seq.Cons ((j, d), tl) ->
                ok := false;
                preferences.(i) <- tl;
                try_marry i j d
        done
      done;

      let actually_missing = List.filteri (fun i _ -> not is_married.(i)) missings in
      let name_changes = ref [] in
      for j = 0 to n - 1 do
        match marriages.(j) with
        | None -> ()
        | Some (i, _) ->
            name_changes := (added_fields.(j), field_name missing_fields.(i)) :: !name_changes
      done;

      {
        add = actually_missing;
        rename = !name_changes;
      }
    in

    let greedy () =
      let rec list_extract predicate l =
        match l with
        | [] -> None
        | hd :: tl when predicate hd -> Some (hd, tl)
        | hd :: tl -> (
            match list_extract predicate tl with
            | None -> None
            | Some (x, tl') -> Some (x, hd :: tl'))
      in

      let compute_distance expected_field added_field =
        if compatibility_test expected_field added_field then
          Misc.Maybe_infinite.of_option (Misc.edit_distance (field_name expected_field) (field_name added_field) cutoff)
        else
          Misc.Maybe_infinite.Infinity ()
      in

      let remaining_added_fields = ref additions in
      let name_changes = ref [] in
      let actually_missing =
        List.filter
          (fun missing_field ->
            match
              list_extract
                (fun added_field ->
                  compute_distance missing_field added_field
                    < Misc.Maybe_infinite.Finite cutoff)
                !remaining_added_fields
            with
            | None -> true
            | Some (added_field, additions) ->
                name_changes := (added_field, field_name missing_field) :: !name_changes;
                remaining_added_fields := additions;
                false)
          missings;
      in

      {
        add = actually_missing;
        rename = !name_changes;
      }
    in

    if m * n <= 1_000_000 then
      stable_marriages ()
    else
      greedy ()
  in

  let suggestion_for_any_order destructor compatibility_test =
    let missing_fields = List.filter_map destructor sgs.missings in
    let added_fields = List.filter_map destructor sgs.additions in

    let suggestions = fuzzy_match_names compatibility_test missing_fields added_fields in

    List.map
      (Location.msg "%a" suggest_adding_field)
      (List.map (fun field -> field.item) suggestions.add)
    @ List.map
      (Location.msg "%a" suggest_renaming_field)
      (List.map (fun (field, suggested_name) -> field.item, suggested_name) suggestions.rename)
  in

  let suggestions_for_first_order destructor compatibility_test =
    suggestion_for_any_order
      (fun item -> Option.map (fun (item, value, type_) -> { item; value; type_ }) (destructor item))
      compatibility_test
  in

  let suggestions_for_second_order destructor compatibility_test =
    suggestion_for_any_order
      (fun item -> Option.map (fun (item, value) -> { item; value; type_ = () }) (destructor item))
      compatibility_test
  in

  Printtyp.wrap_printing_env ~error:true sgs.env (fun () ->
      match sgs.missings, sgs.incompatibles with
      | _ :: _, _ ->
        let type_suggestions =
          suggestions_for_second_order
            (fun item ->
              match item with
              | Types.Sig_type  (_, decl, _, _) -> Some (item, decl)
              | _ -> None)
            (fun expected gotten ->
              let id, loc, _ = Includemod.item_ident_name gotten.item in
              match
                Includemod.type_declarations
                  ~mark:Mark_neither ~loc
                  sgs.env sgs.subst id
                  gotten.value expected.value
              with
              | Ok _ -> true
              | Error _ -> false)
        in

        let module_type_suggestions =
          suggestions_for_second_order
            (fun item ->
              match item with
              | Types.Sig_modtype (_, decl, _) -> Some (item, decl)
              | _ -> None)
            (fun expected gotten ->
              let _, loc, _ = Includemod.item_ident_name gotten.item in
              Includemod.is_modtype_eq
                ~loc sgs.env ~mark:Mark_neither sgs.subst
                (Option.get gotten.value.Types.mtd_type)
                (Option.get expected.value.Types.mtd_type))
        in

        let class_type_suggestions =
          suggestions_for_second_order
            (fun item ->
              match item with
              | Types.Sig_class_type (_, decl, _, _) -> Some (item, decl)
              | _ -> None)
            (fun expected gotten ->
              let _, loc, _ = Includemod.item_ident_name gotten.item in
              match
                Includemod.class_type_declarations
                  ~loc ~old_env:sgs.env sgs.env sgs.subst
                  gotten.value expected.value
              with
              | Ok _ -> true
              | Error _ -> false)
        in

        let value_suggestions =
          suggestions_for_first_order
            (fun item ->
              match item with
              | Types.Sig_value (_, desc, _) ->
                  Some (item, desc, desc.val_type)
              | _ -> None)
            (fun expected gotten ->
              let id, loc, _ = Includemod.item_ident_name gotten.item in
              match
                Includemod.value_descriptions
                  ~mark:Mark_neither ~loc
                  sgs.env sgs.subst id
                  gotten.value expected.value
              with
              | Ok _ -> true
              | Error _ -> false)
        in

        let value_type_changes =
          sgs.incompatibles
          |> List.filter_map (function
            | id, Includemod.Error.Core (Includemod.Error.Value_descriptions {expected; _}) -> Some (id, expected.val_type)
            | _ -> None)
        in

        let module_suggestions =
          suggestions_for_first_order
            (fun item ->
              match item with
              | Types.Sig_module (_, _, decl, _, _) ->
                  Some (item, decl, decl.md_type)
              | _ -> None)
            (fun expected gotten ->
              let _, loc, _ = Includemod.item_ident_name gotten.item in
              Includemod.is_modtype_eq
                ~loc sgs.env ~mark:Mark_neither sgs.subst
                gotten.type_
                expected.type_)
        in

        let class_suggestions =
          suggestions_for_first_order
            (fun item ->
              match item with
              | Types.Sig_class (_, decl, _, _) ->
                  Some (item, decl, decl.cty_type)
              | _ -> None)
            (fun expected gotten ->
              let _, loc, _ = Includemod.item_ident_name gotten.item in
              match
                Includemod.class_declarations
                  ~old_env:sgs.env sgs.env sgs.subst
                  expected.value gotten.value
              with
              | Ok _ -> true
              | Error _ -> false)
        in

        if expansion_token then
          []
          @ class_suggestions
          @ module_suggestions
          @ value_suggestions
          @ List.map (Location.msg "%a" suggest_changing_value_type) value_type_changes
          @ class_type_suggestions
          @ module_type_suggestions
          @ type_suggestions
          @ before
        else
          before
      | [], a :: _ -> sigitem ~expansion_token ~env:sgs.env ~before ~ctx a
      | [], [] -> assert false
    )

and sigitem ~expansion_token ~env ~before ~ctx (name,s) = match s with
  | Core c ->
      dwith_context ctx (core env name c) :: before
  | Module_type diff ->
      module_type ~expansion_token ~eqmode:false ~env ~before
        ~ctx:(Context.Module name :: ctx) diff
  | Module_type_declaration diff ->
      module_type_decl ~expansion_token ~env ~before ~ctx name diff

and module_type_decl ~expansion_token ~env ~before ~ctx id diff =
  let next =
    dwith_context_and_elision ctx (module_type_declarations id) diff in
  let before = next :: before in
  match diff.symptom with
  | Not_less_than mts ->
      let before =
        Location.msg "The first module type is not included in the second"
        :: before
      in
      module_type ~expansion_token ~eqmode:true ~before ~env
        ~ctx:(Context.Modtype id :: ctx) mts
  | Not_greater_than mts ->
      let before =
        Location.msg "The second module type is not included in the first"
        :: before in
      module_type ~expansion_token ~eqmode:true ~before ~env
        ~ctx:(Context.Modtype id :: ctx) mts
  | Incomparable mts ->
      module_type ~expansion_token ~eqmode:true ~env ~before
        ~ctx:(Context.Modtype id :: ctx) mts.less_than
  | Illegal_permutation c ->
      begin match diff.got.Types.mtd_type with
      | None -> assert false
      | Some mty ->
          with_context (Modtype id::ctx)
            (Illegal_permutation.pp Context.alt_pp env) (mty,c)
          :: before
      end

and functor_arg_diff ~expansion_token env (patch: _ Diffing.change) =
  match patch with
  | Insert mty -> Functor_suberror.Inclusion.insert mty
  | Delete mty -> Functor_suberror.Inclusion.delete mty
  | Keep (x, y, _) ->  Functor_suberror.Inclusion.ok x y
  | Change (_, _, Err.Incompatible_params (i,_)) ->
      Functor_suberror.Inclusion.incompatible i
  | Change (g, e,  Err.Mismatch mty_diff) ->
      let more () =
        subcase_list @@
        module_type_symptom ~eqmode:false ~expansion_token ~env ~before:[]
          ~ctx:[] mty_diff.symptom
      in
      Functor_suberror.Inclusion.diff g e more

let functor_app_diff ~expansion_token env  (patch: _ Diffing.change) =
  match patch with
  | Insert mty ->  Functor_suberror.App.insert mty
  | Delete mty ->  Functor_suberror.App.delete mty
  | Keep (x, y, _) ->  Functor_suberror.App.ok x y
  | Change (_, _, Err.Incompatible_params (i,_)) ->
      Functor_suberror.App.incompatible i
  | Change (g, e,  Err.Mismatch mty_diff) ->
      let more () =
        subcase_list @@
        module_type_symptom ~eqmode:false ~expansion_token ~env ~before:[]
          ~ctx:[] mty_diff.symptom
      in
      Functor_suberror.App.diff g e more

let module_type_subst ~env id diff =
  match diff.symptom with
  | Not_less_than mts ->
      module_type ~expansion_token:true ~eqmode:true ~before:[] ~env
        ~ctx:[Modtype id] mts
  | Not_greater_than mts ->
      module_type ~expansion_token:true ~eqmode:true ~before:[] ~env
        ~ctx:[Modtype id] mts
  | Incomparable mts ->
      module_type ~expansion_token:true ~eqmode:true ~env ~before:[]
        ~ctx:[Modtype id] mts.less_than
  | Illegal_permutation c ->
      let mty = diff.got in
      let main =
        with_context [Modtype id]
          (Illegal_permutation.pp Context.alt_pp env) (mty,c) in
      [main]

let all env = function
  | In_Compilation_unit diff ->
      let first = Location.msg "%a" interface_mismatch diff in
      signature ~expansion_token:true ~env ~before:[first] ~ctx:[] diff.symptom
  | In_Type_declaration (id,reason) ->
      [Location.msg "%t" (core env id reason)]
  | In_Module_type diff ->
      module_type ~expansion_token:true ~eqmode:false ~before:[] ~env ~ctx:[]
        diff
  | In_Module_type_substitution (id,diff) ->
      module_type_subst ~env id diff
  | In_Signature diff ->
      signature ~expansion_token:true ~before:[] ~env ~ctx:[] diff
  | In_Expansion cmts ->
      match core_module_type_symptom cmts with
      | None -> assert false
      | Some main -> [Location.msg "%t" main]

(* General error reporting *)

let err_msgs (env, err) =
  Printtyp.Conflicts.reset();
  Printtyp.wrap_printing_env ~error:true env
    (fun () -> coalesce @@ all env err)

let report_error err =
  let main = err_msgs err in
  Location.errorf ~loc:Location.(in_file !input_name) "%t" main

let report_apply_error ~loc env (app_name, mty_f, args) =
  let d = Functor_suberror.App.patch env ~f:mty_f ~args in
  match d with
  (* We specialize the one change and one argument case to remove the
     presentation of the functor arguments *)
  | [ _,  Change (_, _, Err.Incompatible_params (i,_)) ] ->
      Location.errorf ~loc "%t" (Functor_suberror.App.incompatible i)
  | [ _, Change (g, e,  Err.Mismatch mty_diff) ] ->
      let more () =
        subcase_list @@
        module_type_symptom ~eqmode:false ~expansion_token:true ~env ~before:[]
          ~ctx:[] mty_diff.symptom
      in
      Location.errorf ~loc "%t" (Functor_suberror.App.single_diff g e more)
  | _ ->
      let not_functor =
        List.for_all (function _, Diffing.Delete _ -> true | _ -> false) d
      in
      if not_functor then
        match app_name with
        | Includemod.Named_leftmost_functor lid ->
            Location.errorf ~loc
              "@[The module %a is not a functor, it cannot be applied.@]"
               (Style.as_inline_code Printtyp.longident)  lid
        | Includemod.Anonymous_functor
        | Includemod.Full_application_path _
          (* The "non-functor application in term" case is directly handled in
             [Env] and it is the only case where we have a full application
             path at hand. Thus this case of the or-pattern is currently
             unreachable and we don't try to specialize the corresponding error
             message. *) ->
            Location.errorf ~loc
              "@[This module is not a functor, it cannot be applied.@]"
      else
        let intro ppf =
          match app_name with
          | Includemod.Anonymous_functor ->
              Format.fprintf ppf "This functor application is ill-typed."
          | Includemod.Full_application_path lid ->
              Format.fprintf ppf "The functor application %a is ill-typed."
                (Style.as_inline_code Printtyp.longident) lid
          |  Includemod.Named_leftmost_functor lid ->
              Format.fprintf ppf
                "This application of the functor %a is ill-typed."
                 (Style.as_inline_code Printtyp.longident) lid
        in
        let actual = Functor_suberror.App.got d in
        let expected = Functor_suberror.expected d in
        let sub =
          List.rev @@
          Functor_suberror.params functor_app_diff env ~expansion_token:true d
        in
        Location.errorf ~loc ~sub
          "@[<hv>%t@ \
           These arguments:@;<1 2>@[%t@]@ \
           do not match these parameters:@;<1 2>@[functor@ %t@ -> ...@]@]"
          intro
          actual expected

let register () =
  Location.register_error_of_exn
    (function
      | Includemod.Error err -> Some (report_error err)
      | Includemod.Apply_error {loc; env; app_name; mty_f; args} ->
          Some (Printtyp.wrap_printing_env env ~error:true (fun () ->
              report_apply_error ~loc env (app_name, mty_f, args))
            )
      | _ -> None
    )
