(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 2001 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

open Printf

let mklib out files opts =
  if Config.ccomp_type = "msvc"
  then let machine =
    if Config.architecture="amd64"
    then "-machine:AMD64 "
    else ""
  in
  Printf.sprintf "link -lib -nologo %s-out:%s %s %s" machine out opts files
  else Printf.sprintf "%s rcs %s %s %s" Config.ar out opts files

(* PR#4783: under Windows, don't use absolute paths because we do
   not know where the binary distribution will be installed. *)
let compiler_path name =
  if Sys.os_type = "Win32" then name else Filename.concat Config.bindir name

let bytecode_objs = ref []  (* .cmo,.cma,.ml,.mli files to pass to ocamlc *)
and native_objs = ref []    (* .cmx,.ml,.mli files to pass to ocamlopt *)
and c_objs = ref []         (* .o, .a, .obj, .lib, .dll, .dylib, .so files to
                               pass to mkdll and ar *)
and caml_libs = ref []      (* -cclib to pass to ocamlc, ocamlopt *)
and caml_opts = ref []      (* -ccopt to pass to ocamlc, ocamlopt *)
and dynlink = ref Config.supports_shared_libraries
and failsafe = ref false    (* whether to fall back on static build only *)
and c_libs = ref []         (* libs to pass to mkdll and ocamlc -cclib *)
and c_Lopts = ref []      (* options to pass to mkdll and ocamlc -cclib *)
and c_opts = ref []       (* options to pass to mkdll and ocamlc -ccopt *)
and ld_opts = ref []        (* options to pass only to the linker *)
and ocamlc = ref (compiler_path "ocamlc")
and ocamlc_opts = ref []    (* options to pass only to ocamlc *)
and ocamlopt = ref (compiler_path "ocamlopt")
and ocamlopt_opts = ref []  (* options to pass only to ocamlc *)
and output = ref "a"        (* Output name for OCaml part of library *)
and output_c = ref ""       (* Output name for C part of library *)
and rpath = ref []          (* rpath options *)
and debug = ref false       (* -g option *)
and verbose = ref false

let starts_with s pref =
  String.length s >= String.length pref &&
  String.sub s 0 (String.length pref) = pref
let ends_with = Filename.check_suffix
let chop_prefix s pref =
  String.sub s (String.length pref) (String.length s - String.length pref)

exception Bad_argument of string

let print_version () =
  printf "ocamlmklib, version %s\n" Sys.ocaml_version;
  exit 0

let print_version_num () =
  printf "%s\n" Sys.ocaml_version;
  exit 0

let parse_arguments argv =
  let args = Stack.create () in
  let push_args ~first arr =
    for i = Array.length arr - 1 downto first do
      Stack.push arr.(i) args
    done
  in
  let next_arg s =
    if Stack.is_empty args
    then raise (Bad_argument("Option " ^ s ^ " expects one argument"));
    Stack.pop args
  in
  push_args ~first:1 argv;
  while not (Stack.is_empty args) do
    let s = Stack.pop args in
    if s = "-args" then
      push_args ~first:0 (Arg.read_arg (next_arg s))
    else if s = "-args0" then
      push_args ~first:0 (Arg.read_arg0 (next_arg s))
    else if ends_with s ".cmo" || ends_with s ".cma" then
      bytecode_objs := s :: !bytecode_objs
    else if ends_with s ".cmx" then
      native_objs := s :: !native_objs
    else if ends_with s ".ml" || ends_with s ".mli" then
     (bytecode_objs := s :: !bytecode_objs;
      native_objs := s :: !native_objs)
    else if List.exists (ends_with s)
                        [".o"; ".a"; ".obj"; ".lib"; ".dll"; ".dylib"; ".so"]
    then
      c_objs := s :: !c_objs
    else if s = "-cclib" then
      caml_libs := next_arg s :: "-cclib" :: !caml_libs
    else if s = "-ccopt" then
      caml_opts := next_arg s :: "-ccopt" :: !caml_opts
    else if s = "-custom" then
      dynlink := false
    else if s = "-I" then
      caml_opts := next_arg s :: "-I" :: !caml_opts
    else if s = "-failsafe" then
      failsafe := true
    else if s = "-g" then
      debug := true
    else if s = "-h" || s = "-help" || s = "--help" then
      raise (Bad_argument "")
    else if s = "-ldopt" then
      ld_opts := next_arg s :: !ld_opts
    else if s = "-linkall" then
      caml_opts := s :: !caml_opts
    else if starts_with s "-l" then
      let s =
        if Config.ccomp_type = "msvc" then
          String.sub s 2 (String.length s - 2) ^ ".lib"
        else
          s
      in
      c_libs := s :: !c_libs
    else if starts_with s "-L" then
     (c_Lopts := s :: !c_Lopts;
      let l = chop_prefix s "-L" in
      if not (Filename.is_relative l) then rpath := l :: !rpath)
    else if s = "-ocamlcflags" then
      ocamlc_opts := next_arg s :: !ocamlc_opts
    else if s = "-ocamlc" then
      ocamlc := next_arg s
    else if s = "-ocamlopt" then
      ocamlopt := next_arg s
    else if s = "-ocamloptflags" then
      ocamlopt_opts := next_arg s :: !ocamlopt_opts
    else if s = "-o" then
      output := next_arg s
    else if s = "-oc" then
      output_c := next_arg s
    else if s = "-dllpath" || s = "-R" || s = "-rpath" then
      rpath := next_arg s :: !rpath
    else if starts_with s "-R" then
      rpath := chop_prefix s "-R" :: !rpath
    else if s = "-Wl,-rpath" then
     (let a = next_arg s in
      if starts_with a "-Wl,"
      then rpath := chop_prefix a "-Wl," :: !rpath
      else raise (Bad_argument("Option -Wl,-rpath expects a -Wl, argument")))
    else if starts_with s "-Wl,-rpath," then
      rpath := chop_prefix s "-Wl,-rpath," :: !rpath
    else if starts_with s "-Wl,-R" then
      rpath := chop_prefix s "-Wl,-R" :: !rpath
    else if s = "-v" || s = "-verbose" then
      verbose := true
    else if s = "-version" then
      print_version ()
    else if s = "-vnum" then
      print_version_num ()
    else if starts_with s "-F" then
      c_opts := s :: !c_opts
    else if s = "-framework" then
      (let a = next_arg s in c_opts := a :: s :: !c_opts)
    else if starts_with s "-" then
      prerr_endline ("Unknown option " ^ s)
    else
      raise (Bad_argument("Don't know what to do with " ^ s))
  done;
  List.iter
    (fun r -> r := List.rev !r)
    [ bytecode_objs; native_objs; caml_libs; caml_opts;
      c_libs; c_objs; c_opts; ld_opts; rpath ];
(* Put -L options in front of -l options in -cclib to mimic -ccopt behavior *)
  c_libs := !c_Lopts @ !c_libs;

  if !output_c = "" then output_c := !output

let usage =
{|Usage: ocamlmklib [options] <.cmo|.cma|.cmx|.ml|.mli|.o|.a|.obj|.lib|
                             .dll|.dylib files>
Options are:
  -args <file>   Read additional newline-terminated command line arguments
                 from <file>
  -args0 <file>  Read additional null character terminated command line
                 arguments from <file>
  -cclib <lib>   C library passed to ocamlc -a or ocamlopt -a only
  -ccopt <opt>   C option passed to ocamlc -a or ocamlopt -a only
  -custom        Disable dynamic loading
  -g             Build with debug information
  -dllpath <dir> Add <dir> to the run-time search path for DLLs
  -F<dir>        Specify a framework directory (MacOSX)
  -framework <name>    Use framework <name> (MacOSX)
  -help          Print this help message and exit
  --help         Same as -help
  -h             Same as -help
  -I <dir>       Add <dir> to the path searched for OCaml object files
  -failsafe      fall back to static linking if DLL construction failed
  -ldopt <opt>   C option passed to the shared linker only
  -linkall       Build OCaml archive with link-all behavior
  -l<lib>        Specify a dependent C library
  -L<dir>        Add <dir> to the path searched for C libraries
  -ocamlc <cmd>  Use <cmd> in place of "ocamlc"
  -ocamlcflags <opt>    Pass <opt> to ocamlc
  -ocamlopt <cmd> Use <cmd> in place of "ocamlopt"
  -ocamloptflags <opt>  Pass <opt> to ocamlopt
  -o <name>      Generated OCaml library is named <name>.cma or <name>.cmxa
  -oc <name>     Generated C library is named dll<name>.so or lib<name>.a
  -rpath <dir>   Same as -dllpath <dir>
  -R<dir>        Same as -rpath
  -verbose       Print commands before executing them
  -v             same as -verbose
  -version       Print version and exit
  -vnum          Print version number and exit
  -Wl,-rpath,<dir>     Same as -dllpath <dir>
  -Wl,-rpath -Wl,<dir> Same as -dllpath <dir>
  -Wl,-R<dir>          Same as -dllpath <dir>
|}

let command cmd =
  if !verbose then (print_string "+ "; print_string cmd; print_newline());
  Sys.command cmd

let scommand cmd =
  if command cmd <> 0 then exit 2

let safe_remove s =
  try Sys.remove s with Sys_error _ -> ()

let make_set l =
  let rec merge l = function
    []     -> List.rev l
  | p :: r -> if List.mem p l then merge l r else merge (p::l) r
  in
  merge [] l

let make_rpath flag =
  if !rpath = [] || flag = ""
  then ""
  else flag ^ String.concat ":" (make_set !rpath)

let make_rpath_ccopt flag =
  if !rpath = [] || flag = ""
  then ""
  else "-ccopt " ^ flag ^ String.concat ":" (make_set !rpath)

let prefix_list pref l =
  List.map (fun s -> pref ^ s) l

let prepostfix pre name post =
  let base = Filename.basename name in
  let dir = Filename.dirname name in
  Filename.concat dir (pre ^ base ^ post)

let transl_path s =
  match Sys.os_type with
    | "Win32" ->
        let s = Bytes.of_string s in
        let rec aux i =
          if i = Bytes.length s || Bytes.get s i = ' ' then s
          else begin
            if Bytes.get s i = '/' then Bytes.set s i '\\';
            aux (i + 1)
          end
        in Bytes.to_string (aux 0)
    | _ -> s

let flexdll_dirs =
  let dirs =
    let expand = Misc.expand_directory Config.standard_library in
    List.map expand Config.flexdll_dirs
  in
  let f dir =
    let dir =
      if String.contains dir ' ' then
        "\"" ^ dir ^ "\""
      else
        dir
    in
      "-L" ^ dir
  in
  List.map f dirs

let build_libs () =
  if !c_objs <> [] then begin
    if !dynlink then begin
      let retcode = command
          (Printf.sprintf "%s %s -o %s %s %s %s %s %s %s"
             Config.mkdll
             (if !debug then "-g" else "")
             (prepostfix "dll" !output_c Config.ext_dll)
             (String.concat " " !c_objs)
             (String.concat " " !c_opts)
             (String.concat " " !ld_opts)
             (make_rpath Config.mksharedlibrpath)
             (String.concat " " !c_libs)
             (String.concat " " flexdll_dirs)
          )
      in
      if retcode <> 0 then if !failsafe then dynlink := false else exit 2
    end;
    safe_remove (prepostfix "lib" !output_c Config.ext_lib);
    scommand
      (mklib (prepostfix "lib" !output_c Config.ext_lib)
             (String.concat " " !c_objs) "");
  end;
  if !bytecode_objs <> [] then
    scommand
      (sprintf "%s -a %s %s %s -o %s.cma %s %s -dllib -l%s -cclib -l%s \
                   %s %s %s %s"
                  (transl_path !ocamlc)
                  (if !debug then "-g" else "")
                  (if !dynlink then "" else "-custom")
                  (String.concat " " !ocamlc_opts)
                  !output
                  (String.concat " " !caml_opts)
                  (String.concat " " !bytecode_objs)
                  (Filename.basename !output_c)
                  (Filename.basename !output_c)
                  (String.concat " " (prefix_list "-ccopt " !c_opts))
                  (make_rpath_ccopt Config.default_rpath)
                  (String.concat " " (prefix_list "-cclib " !c_libs))
                  (String.concat " " !caml_libs));
  if !native_objs <> [] then
    scommand
      (sprintf "%s -a %s %s -o %s.cmxa %s %s -cclib -l%s %s %s %s %s"
                  (transl_path !ocamlopt)
                  (if !debug then "-g" else "")
                  (String.concat " " !ocamlopt_opts)
                  !output
                  (String.concat " " !caml_opts)
                  (String.concat " " !native_objs)
                  (Filename.basename !output_c)
                  (String.concat " " (prefix_list "-ccopt " !c_opts))
                  (make_rpath_ccopt Config.default_rpath)
                  (String.concat " " (prefix_list "-cclib " !c_libs))
                  (String.concat " " !caml_libs))

let main () =
  try
    parse_arguments Sys.argv;
    build_libs()
  with
  | Bad_argument "" ->
      prerr_string usage; exit 0
  | Bad_argument s ->
      prerr_endline s; prerr_string usage; exit 4
  | Sys_error s ->
      prerr_string "System error: "; prerr_endline s; exit 4
  | x ->
      raise x

let _ = main ()
