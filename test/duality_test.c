#include "z3.h"

int main ()
{
    Z3_config conf = Z3_mk_config();
    Z3_context c = Z3_mk_context(conf);
    
    Z3_params p = Z3_mk_params(c);
    Z3_params_inc_ref(c, p);
    Z3_fixedpoint fp = Z3_mk_fixedpoint(c);
    Z3_params_set_uint(c, p, Z3_mk_string_symbol(c, "fixedpoint.timeout"), 3000);
    Z3_params_set_symbol(c, p, Z3_mk_string_symbol(c, "fixedpoint.engine"), Z3_mk_string_symbol(c, "duality"));
    Z3_fixedpoint_set_params(c, fp, p);
    
    Z3_sort Int = Z3_mk_int_sort(c);
    Z3_sort IntInt[2] = {Int, Int};
    Z3_sort Bool = Z3_mk_bool_sort(c);

    Z3_func_decl P = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "P"),
                                     2, IntInt, Bool);
    Z3_func_decl P2 = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "P"),
                                      2, IntInt, Bool);
    Z3_func_decl Q = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "Q"),
                                     2, IntInt, Bool);
    Z3_func_decl Goal = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "Goal"),
                                        2, IntInt, Bool);
    Z3_fixedpoint_register_relation(c, fp, P);
    Z3_fixedpoint_register_relation(c, fp, P2);
    Z3_fixedpoint_register_relation(c, fp, Q);
    Z3_fixedpoint_register_relation(c, fp, Goal);    

    Z3_func_decl x_ = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "x"), 0, NULL, Int);
    Z3_func_decl y_ = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "y"), 0, NULL, Int);
    Z3_func_decl z_ = Z3_mk_func_decl(c, Z3_mk_string_symbol(c, "z"), 0, NULL, Int);
    Z3_ast x = Z3_mk_app(c, x_, 0, NULL);
    Z3_ast y = Z3_mk_app(c, y_, 0, NULL);
    Z3_ast z = Z3_mk_app(c, z_, 0, NULL);
    Z3_fixedpoint_register_variable(c, fp, x_);
    Z3_fixedpoint_register_variable(c, fp, y_);
    Z3_fixedpoint_register_variable(c, fp, z_);
    
    Z3_ast xy_args[2] = {x,y};
    Z3_ast xz_args[2] = {x,z};
    Z3_ast yz_args[2] = {y,z};
    Z3_ast y1_args[2] = {y,Z3_mk_int(c, 1, Int)};
    Z3_ast and_args1[2] = {Z3_mk_app(c, P, 2, xy_args), Z3_mk_eq(c,z,Z3_mk_add(c, 2, y1_args))};
    Z3_ast and_args2[2] = {Z3_mk_app(c, P, 2, xy_args), Z3_mk_app(c, P2, 2, yz_args)};
    Z3_fixedpoint_add_rule(c, fp,
                           Z3_mk_implies(c, Z3_mk_app(c, P, 2, xy_args), Z3_mk_app(c, P2, 2, xy_args)),
                           Z3_mk_string_symbol(c, "ra"));
    Z3_fixedpoint_add_rule(c, fp,
                           Z3_mk_implies(c, Z3_mk_app(c, P2, 2, xy_args), Z3_mk_app(c, P, 2, xy_args)),
                           Z3_mk_string_symbol(c, "rb"));
    Z3_fixedpoint_add_rule(c, fp,
                           Z3_mk_implies(c, Z3_mk_eq(c,x,y), Z3_mk_app(c, P, 2, xy_args)),
                           Z3_mk_string_symbol(c, "r1"));
    Z3_fixedpoint_add_rule(c, fp,
                           Z3_mk_implies(c, Z3_mk_and(c, 2, and_args1), Z3_mk_app(c, P, 2, xz_args)),
                           Z3_mk_string_symbol(c, "r2"));
    Z3_fixedpoint_add_rule(c, fp,
                           Z3_mk_implies(c, Z3_mk_and(c, 2, and_args2), Z3_mk_app(c, Q, 2, xz_args)),
                           Z3_mk_string_symbol(c, "r3"));

    Z3_ast theSafety = Z3_mk_implies(c, Z3_mk_app(c, Q, 2, xz_args), Z3_mk_le(c,x,z));
    Z3_fixedpoint_add_rule(c, fp,
                           Z3_mk_implies(c, Z3_mk_not(c, theSafety), Z3_mk_app(c, Goal, 2, xz_args)),
                           Z3_mk_string_symbol(c, "r4"));

    Z3_lbool res = Z3_fixedpoint_query(c, fp, Z3_mk_app(c, Goal, 2, xz_args));
    if (res == Z3_L_TRUE)
        printf("sat (unsafe)\n");
    else if (res == Z3_L_FALSE)
        printf("unsat (safe)\n");
    else
        printf("unknown\n");
    
    return 0;
}

