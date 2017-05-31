#directory "/home/caleb/repos/z3/build/api/ml";;
#load "nums.cma";;
#load "z3ml.cma";;

open Z3;;
open Fixedpoint;;
open Params;;
open Symbol;;
open FuncDecl;;
open Arithmetic;;
open Boolean;;
       
let c = mk_context [] in
let fp = mk_fixedpoint c in
let p = mk_params c in
  add_int p (mk_string c "fixedpoint.timeout") 3000;
  add_symbol p (mk_string c "fixedpoint.engine") (mk_string c "duality");
  set_parameters fp p;

  let sint = Integer.mk_sort c in
  let sbool = Boolean.mk_sort c in
  
  let predP = mk_func_decl c (mk_string c "P") [sint; sint] sbool in
  let predP2 = mk_func_decl c (mk_string c "P2") [sint; sint] sbool in
  let predQ = mk_func_decl c (mk_string c "Q") [sint; sint] sbool in
  let predGoal = mk_func_decl c (mk_string c "Goal") [sint; sint] sbool in
  
    register_relation fp predP;
    register_relation fp predP2;
    register_relation fp predQ;
    register_relation fp predGoal;

    let x_ = mk_func_decl c (mk_string c "x") [] sint in
    let y_ = mk_func_decl c (mk_string c "y") [] sint in
    let z_ = mk_func_decl c (mk_string c "z") [] sint in
    let x = apply x_ [] in
    let y = apply y_ [] in
    let z = apply z_ [] in
      register_variable fp x_;
      register_variable fp y_;
      register_variable fp z_;

      add_rule fp (mk_implies c (apply predP [x; y]) (apply predP2 [x; y])) None;
      add_rule fp (mk_implies c (apply predP2 [x; y]) (apply predP [x; y])) None;

      add_rule fp (mk_implies c (mk_eq c x y) (apply predP [x; y])) None;
      add_rule fp (mk_implies c (mk_and c [apply predP [x; y];
                                           mk_eq c z (mk_add c [y; Integer.mk_numeral_i c 1])])
                              (apply predP [x; z])) None;
      add_rule fp (mk_implies c (mk_and c [apply predP [x; y]; apply predP [y; z]])
                              (apply predQ [x; z])) None;
     
      let theSafety = mk_implies c (apply predQ [x; z]) (mk_le c x z) in
        add_rule fp (mk_implies c (mk_not c theSafety) (apply predGoal [x; z])) None;
        
        let res = query fp (apply predGoal [x; z]) in
        match res with
        | Solver.SATISFIABLE -> Printf.printf("sat (unsafe)\n")
        | Solver.UNSATISFIABLE -> Printf.printf("unsat (safe)\n")
        | _ -> Printf.printf("unknown\n")
