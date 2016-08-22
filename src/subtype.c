// This file is a part of Julia. License is MIT: http://julialang.org/license

/*
  subtyping predicate
*/
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#ifdef _OS_WINDOWS_
#include <malloc.h>
#endif
#include "julia.h"
#include "julia_internal.h"

typedef struct {
    int depth;
    int8_t more;
    int stacksize;
    uint32_t stack[10];
} jl_unionstate_t;

typedef struct _varbinding {
    jl_value_t *tv;
    jl_value_t *lb;
    jl_value_t *ub;
    int8_t right;
    struct _varbinding *prev;
} jl_varbinding_t;

typedef struct {
    jl_varbinding_t *vars;
    jl_unionstate_t Lunions;
    jl_unionstate_t Runions;
    int8_t outer;
} jl_stenv_t;

static int subtype_union(jl_value_t *t, jl_uniontype_t *u, jl_stenv_t *e, int8_t R, jl_unionstate_t *state)
{
    e->outer = 0;
    if (state->depth >= state->stacksize) {
        state->more = 1;
        return 1;
    }
    int ui = ; // get state.stack[state.depth]
    state->depth++;
    int choice = ui==0 ? u->a : u->b;
    return R ? subtype(t, choice, e) : subtype(choice, t, e);
}

static int jl_is_type(jl_value_t *x)
{
    return jl_is_datatype(x) || jl_is_uniontype(x) || jl_is_unionall(x) || x == jl_bottom_type;
}

static int subtype(jl_value_t *x, jl_value_t *y, jl_stenv_t *e)
{
    /*
    if (x == y) return 1;
    if (x == jl_bottom_type) return 1;
    if (y == jl_any_type) return 1;
    */
    if (jl_is_unionall(x) && jl_is_unionall(y)) {
        return subtype_unionall();
    }
    // take apart unions before handling vars
    if (jl_is_uniontype(x)) {
        if (jl_is_uniontype(y))
            return subtype_union(x, y, e, 1, &e->Runions);
        if (jl_is_unionall(y))
            return subtype_unionall();
        return subtype_union(y, x, e, 0, &e->Lunions);
    }
    if (jl_is_uniontype(y)) {
        //if (x == ((jl_uniontype_t*)y)->a || x == ((jl_uniontype_t*)y)->b)
        //    return 1;
        if (jl_is_unionall(x))
            return subtype_unionall();
        return subtype_union(x, y, e, 1, &e->Runions);
    }
    if (jl_is_typevar(x)) {
        if (jl_is_typevar(y)) {
            e->outer = 0;
            if (x == y) return 1;
            jl_varbinding_t *xx = lookup(e, x);
            jl_varbinding_t *yy = lookup(e, y);
            if (xx->right) {
                if (yy->right) {
                    // this is a bit odd, but seems necessary to make this case work:
                    // (UnionAll x<:T<:x RefT{RefT{T}}) == RefT{UnionAll x<:T<:x RefT{T}}
                    return subtype(yy->ub, yy->lb, e);
                }
                return var_lt(x, y, e);
            }
            else if (!yy->right) {   // check ∀x,y . x<:y
                // the bounds of left-side variables never change, and can only lead
                // to other left-side variables, so using || here is safe.
                return subtype(xx->ub, y, e) || subtype(x, yy->lb, e);
            }
            else {
                return var_gt(y, x, e);
            }
        }
        return var_lt(x, y, e);
    }
    if (jl_is_typevar(y)) {
        return var_gt(y, x, e);
    }
    if (jl_is_datatype(x) && jl_is_datatype(y)) {
        if (y == jl_any_type) return 1;

    }
    if (jl_is_type(x) && jl_is_type(y))
        return x == jl_bottom_type || x == y;
    return x == y || jl_egal(x, y);
}

static int exists_subtype(jl_value_t *x, jl_value_t *y, jl_stenv_t *e, int8_t anyunions)
{
    int exists;
    for (exists=0; exists <= anyunions; exists++) {
        if (e->Runions.stacksize > 0)
            e->Runions.stack[ end ] = exists; // TODO
        e->Lunions.depth = e->Runions.depth = 0;
        e->Lunions.more = e->Runions.more = 0;

        int found = subtype(x, y, e);
        if (e->Lunions.more)
            return 1;
        if (e->Runions.more) {
            // push false into Runions stack
            found = exists_subtype(x, y, e, 1);
            // pop Runions stack
        }
        if (found) return 1;
    }
    return 0;
}

static int forall_exists_subtype(jl_value_t *x, jl_value_t *y, jl_stenv_t *e, int8_t anyunions)
{
    int forall;
    for (forall=0; forall <= anyunions; forall++) {
        if (e->Lunions.stacksize > 0)
            e->Lunions.stack[ end ] = forall; //TODO
        if (!exists_subtype(x, y, e, 0))
            return 0;
        if (e->Lunions.more) {
            // push false into Lunion stack
            int sub = forall_exists_subtype(x, y, e, 1);
            // pop Lunion stack
            if (!sub) return 0;
        }
    }
    return 1;
}

JL_DLLEXPORT int jl_subtype_env(jl_value_t *x, jl_value_t *y, jl_stenv_t *e)
{
    e->vars = NULL;
    e->outer = 1;
    e->Lunions.depth = 0;      e->Runions.depth = 0;
    e->Lunions.more = 0;       e->Runions.more = 0;
    e->Lunions.stacksize = 0;  e->Runions.stacksize = 0;
    return forall_exists_subtype(x, y, e, 0);
}

JL_DLLEXPORT int jl_subtype(jl_value_t *x, jl_value_t *y)
{
    jl_stenv_t e;
    return jl_subtype_env(x, y, &e);
}
