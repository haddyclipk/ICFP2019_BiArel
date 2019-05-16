open OUnit2
module T = Tycheck_sigs
module E = Exist_elim
module SE = Support.Error

let main_debug   fi = SE.message 1 General fi
                    let dp = Support.FileInfo.dummyinfo
exception Success

  let parse_exec file =
  let fh = open_in file in
  let lexbuf = (Lexing.from_channel fh) in
  let (program,cost, unary_ty, mu) as triple =
      try Parser.u_toplevel Lexer.main lexbuf
      with Parsing.Parse_error -> Support.Error.error_msg Support.Options.Parser (Lexer.info lexbuf) "Parse error" in
    Parsing.clear_parser();
    close_in fh;
    triple

      
let parse_diff file =
  let fh = open_in file in
  let lexbuf = (Lexing.from_channel fh) in
  let (program1, program2, cost, binary_ty) as quad =
    try Parser.b_toplevel Lexer.main lexbuf
    with Parsing.Parse_error -> Support.Error.error_msg Support.Options.Parser (Lexer.info lexbuf) "Parse error" in
   Parsing.clear_parser();
   close_in fh;
   quad
       
let run_unary_test infile =
  let (prgm, cost, uty, mu) = parse_exec infile in
   main_debug dp "U Parsed program:@\n@[%a@]@.\nParsed type:@\n@[%a@]@." 
	       Print.pp_expr prgm Print.pp_utype uty;
    let ctx = Ctx.set_exec_mode mu (Ctx.empty_context) in
    let cs =  (Unary.check_type ctx prgm uty (Some cost)) in
    E.elim ctx (cs)
              (fun cs' -> 
                let elim_cs = Constr.constr_simpl cs' in 
                if ((WhySolver.send_smt_u) elim_cs) then raise Success else ())

let recordResults test totalT typeChT  existT  csT =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "results.txt" in
  let fmt = format_of_string "%s & %0.2f & %0.2f & %0.2f & %0.2f \\\\ \\hline \n" in
  let r = Str.regexp "examples/binary/\\(.*\\).br" in
  let name =   Str.replace_first r "\kw{\\1}" test in 
  output_string oc (Printf.sprintf fmt ("$" ^name ^ "$") (totalT) typeChT  existT  csT );
  close_out oc

            
let run_binary_test infile heur =
    let t= Unix.gettimeofday ()  in
    let (prgm1, prgm2, cost, bty) = parse_diff infile in
    main_debug dp "B Parsed programs:@\n@[%a@]@ @\n@\n@[%a@]@." 
	       Print.pp_expr prgm1 Print.pp_expr prgm2;
   let ctx = Ctx.set_heur_mode heur (Ctx.empty_context) in
   let cost = Some cost in
   let cs  =  (Binary.check_type ctx prgm1 prgm2 bty cost) in
   let typeChT = (Unix.gettimeofday () -. t) in
   let tcons= Unix.gettimeofday ()  in
   let existT = ref 0.0 in
    E.elim ctx (cs)
         (fun cs' ->
           let elim_cs = Constr.constr_simpl cs' in
           let t'' = Unix.gettimeofday () in
           existT := (t'' -. tcons);
           if ((WhySolver.send_smt) elim_cs) then (recordResults infile (Unix.gettimeofday () -. t) typeChT !existT  (Unix.gettimeofday () -. t'')
; raise Success) else ())




let u_pre s = (fun _ -> run_unary_test ("examples/unary/" ^ s)) 
let b_pre s = (fun _ -> run_binary_test ("examples/binary/" ^ s) Ctx.Usual) 
(* let b_pre_NC s = (fun _ -> run_binary_test ("examples/binary/" ^ s) Ctx.NoChange)  *)


  
let utest_shift utest_ctxt = assert_raises Success (u_pre "monad_shift_max.br");;
let utest_shiftm utest_ctxt = assert_raises Success (u_pre "monad_shift_min.br");;
let utest_insert utest_ctxt = assert_raises Success (u_pre "monad_insert_max.br");;
let utest_insertm utest_ctxt = assert_raises Success (u_pre "monad_insert_min.br");;
let utest_iSort utest_ctxt = assert_raises Success (u_pre "monad_iSort_max.br");;
let utest_iSortm utest_ctxt = assert_raises Success (u_pre "monad_iSort_min.br");;
let utest_map utest_ctxt = assert_raises Success (u_pre "monad_map_max.br");;
let utest_mapm utest_ctxt = assert_raises Success (u_pre "monad_map_min.br");;
let utest_nss utest_ctxt = assert_raises Success (u_pre "monad_nss_helper_max.br");;
let utest_nssm utest_ctxt = assert_raises Success (u_pre "monad_nss_helper_min.br");;
let utest_boolOr utest_ctxt = assert_raises Success (u_pre "monad_boolOr_max.br");;
let utest_boolOrm utest_ctxt = assert_raises Success (u_pre "monad_boolOr_min.br");;

let btest_boolOr btest_ctxt = assert_raises Success  (b_pre "Amonad_boolOr.br");;
let btest_nss btest_ctxt = assert_raises Success  (b_pre "Amonad_nss_helper_precise.br");;
let btest_map btest_ctxt = assert_raises Success  (b_pre "Amonad_map.br");;
let btest_map2 btest_ctxt = assert_raises Success  (b_pre "Amonad_map2.br");;
let btest_merge btest_ctxt = assert_raises Success  (b_pre "Amonad_merge.br");;
let btest_merge2 btest_ctxt = assert_raises Success  (b_pre "Amonad_merge2.br");;
let btest_loop btest_ctxt = assert_raises Success  (b_pre "Amonad_loop.br");;
let btest_seperate btest_ctxt = assert_raises Success  (b_pre "Amonad_separate_pr.br");;
let btest_fft btest_ctxt = assert_raises Success  (b_pre "Amonad_fft.br");;
let btest_sam btest_ctxt = assert_raises Success  (b_pre "Amonad_sam.br");;
let btest_comp btest_ctxt = assert_raises Success  (b_pre "Amonad_comp.br");;


  
(* Tests for maximum execution mode *)
let max_suite =
"suite">:::
 ["test shift1">:: utest_shift;
  "test map1">:: utest_map;
  "test insert1">:: utest_insert;
  "test iSort1">:: utest_iSort;
  "test nss">:: utest_nss;
 ]
;;

(* Tests for minimum execution mode *)
let min_suite =
"suite">:::
  ["test nss [min]">:: utest_nssm;
   "test shift [min]">:: utest_shiftm;
  "test map [min]">:: utest_mapm;
  "test insert [min]">:: utest_insertm;
  "test iSort [min]">:: utest_iSortm;
 ]
;;

(* Tests for diff execution mode *)
let diff_suite =
"suite">:::
  ["test boolOr">:: btest_boolOr;
   "test map">:: btest_map;
   "test map2">:: btest_map2;
   "test nss">:: btest_nss;
   "test merge">:: btest_merge;
    "test merge2">:: btest_merge2;
   "test loop">:: btest_loop;
   "test seperate">:: btest_seperate;
   "test fft">:: btest_fft;
    "test sam">:: btest_sam;
    "test comp">:: btest_comp;
 ]
;;


let () =
  run_test_tt_main max_suite;
  run_test_tt_main min_suite;
  run_test_tt_main diff_suite;
;;
