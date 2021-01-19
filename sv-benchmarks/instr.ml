open Cil
module E = Errormsg
module H = Hashtbl
module P = Printf	     
module L = List
module S = String
module CM = Common	   

let nondet_int_name = "__VERIFIER_nondet_int"
let nondet_uint_name = "__VERIFIER_nondet_uint"
let assert_fail_name = "__assert_fail"

let is_nondet fname =
  fname = nondet_int_name || fname = nondet_uint_name

let is_assert_fail fname = fname = assert_fail_name

let is_builtin fname = is_nondet fname || is_assert_fail fname

let is_int_type typ = 
  match typ with
  | TInt _ -> true
  | _ -> false
 
class add_builtin_body_visitor = object(self)
  inherit nopCilVisitor

  method private create_nondet_body fd ?(is_unsigned=false): stmt list =
    let rand_range = 11 in
    let rt, _, _, _ = splitFunctionType fd.svar.vtype in
    let v1 = makeTempVar fd rt in
    let v2 = makeTempVar fd rt in
    let v1e = CM.expOfVi v1 in
    let v2e = CM.expOfVi v2 in
    let choiceStmt = 
      let rand_fun, rand_args = "rand", [] in
      mkStmtOneInstr (CM.mkCall ~av:(Some (var v1)) rand_fun rand_args)
    in
    let assignStmt = 
      let rhs_exp =
        let range_exp = BinOp(Mod, v1e, integer rand_range, rt) in
        if is_unsigned then
          range_exp
        else
          BinOp(MinusA, range_exp, integer (rand_range/2), rt)
      in
      mkStmtOneInstr (Set (var v2, rhs_exp, !currentLoc)) 
    in
    let retStmt = mkStmt (Return (Some v2e, !currentLoc)) in
    [choiceStmt; assignStmt; retStmt]

  method private create_assert_fail_body fd: stmt list =
    let assertStmt =
      mkStmtOneInstr (CM.mkCall "assert" [integer 0])
    in
    [assertStmt]
    
  method vfunc fd =
    let action fd: fundec = (
      if is_nondet fd.svar.vname then
        fd.sbody.bstmts <- self#create_nondet_body fd ~is_unsigned:(fd.svar.vname = nondet_uint_name)
      else if is_assert_fail fd.svar.vname then	  
        fd.sbody.bstmts <- self#create_assert_fail_body fd
      );
      fd 
    in 
    ChangeDoChildrenPost(fd, action)

  method vglob glob =
    match glob with
    | GVarDecl (vi, loc) ->
      if is_builtin vi.vname then
        let fd = emptyFunction vi.vname in
        print_endline (vi.vname ^ ": " ^ (CM.string_of_typ vi.vtype));
        let ftype = match vi.vtype with
          | TFun (t, args_opt, b, attrs) ->
            (match args_opt with
            | None -> vi.vtype
            | Some args ->
              let nargs = List.map (fun (s, st, sattrs) ->
					let ns = if s = "" then CM.mk_fresh_id () else s in
					(ns, st, sattrs)) args in
              TFun (t, Some nargs, b, attrs))
          | _ -> vi.vtype
        in
        setFunctionTypeMakeFormals fd ftype;
        let stmts =
          if is_nondet vi.vname then 
            self#create_nondet_body fd ~is_unsigned:(fd.svar.vname = nondet_uint_name)
          else if is_assert_fail vi.vname then
            self#create_assert_fail_body fd
          else []
        in
        fd.sbody <- mkBlock stmts;
        ChangeTo [GFun (fd, loc)]
      else DoChildren
    | _ -> DoChildren

end

class is_large_IULong_exp_visitor = object(self)
  inherit nopCilVisitor

  val mutable is_IULong = false

  method vexpr (e: exp) =
    (match e with
    | Const c -> 
      (match c with
      | CInt64 (v, IULong, _) -> 
        let () = print_endline (Int64.to_string v) in
        is_IULong <- true
      | _ -> ())
    | _ -> ());
    DoChildren

  method get_res () = is_IULong
end

let is_large_IULong_exp (e: exp) =
  let iev = new is_large_IULong_exp_visitor in
  ignore (visitCilExpr (iev :> nopCilVisitor) e);
  iev#get_res ()

class change_large_IULong_to_nondet_visitor = object(self)
  inherit nopCilVisitor

  method vinst (i: instr) =
    match i with
    | Set (l, e, _) ->
      if is_large_IULong_exp e then
        let nondet_call = CM.mkCall ~av:(Some l) nondet_int_name [] in
        ChangeTo [nondet_call]
      else SkipChildren
    | Call (l, _, el, _) ->
      if List.exists is_large_IULong_exp el then
        let nondet_call = CM.mkCall ~av:l nondet_int_name [] in
        ChangeTo [nondet_call]
      else SkipChildren
    | _ -> DoChildren
end

let () = 
  begin    
    initCIL();
    Cil.lineDirectiveStyle := None; (* reduce code, remove all junk stuff *)
    Cprint.printLn := false; (* don't print line *)
    (* for Cil to retain &&, ||, ?: instead of transforming them to If stmts *)
    Cil.useLogicalOperators := true;
    Rmtmps.rmUnusedInlines := true;

    let src = Sys.argv.(1) in
    let instr_src = src ^ ".instr.c" in (* instrument for execution *)
    let ast = Frontc.parse src () in

    let includes = ["stdio.h"; "stdlib.h"; "assert.h"; "math.h"] in 
    let includes = L.map (fun x -> "#include \"" ^ x ^ "\"") includes in
    let adds = S.concat "\n" includes in
    ast.globals <- (GText adds)::ast.globals;
    
    let () = ignore (visitCilFile (new add_builtin_body_visitor) ast) in
    let () = ignore (visitCilFile (new change_large_IULong_to_nondet_visitor) ast) in
    CM.writeSrc instr_src ast
  end
