/* vim: set ts=4 sw=4 et tw=80 : */

#include <string.h>
#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <stdlib.h>

#include <gc.h>

typedef uint32_t *box_t;

void *gc_alloc(size_t size) {
    void *p = GC_MALLOC(size);
    assert(p);
    return p;
}

box_t sinter_main();

int main() {
    return *sinter_main();
}

// *Integer
box_t stdlib_multiply_integers(box_t a, box_t b) {
    box_t box = gc_alloc(sizeof(*box));
    *box = *a * *b;
    return box;
}

// +Integer
box_t stdlib_add_integers(box_t a, box_t b) {
    box_t box = gc_alloc(sizeof(*box));
    *box = *a + *b;
    return box;
}

// -Integer
box_t stdlib_subtract_integers(box_t a, box_t b) {
    box_t box = gc_alloc(sizeof(*box));
    *box = *a - *b;
    return box;
}

// <=Integer
box_t stdlib_less_than_or_equal_to_integer(box_t a, box_t b) {
    box_t box = gc_alloc(sizeof(*box));
    *box = *a <= *b ? 1 : 0;
    return box;
}

// ++
box_t stdlib_string_concatenate(box_t a, box_t b) {
    char *ac = (char *) a;
    char *bc = (char *) b;

    size_t n = strlen(ac) + strlen(bc) + 1;

    char *result = gc_alloc(sizeof(char) * n);
    snprintf(result, n, "%s%s", ac, bc);

    return (box_t) result;
}

// Prelude::IO::prim__putStr
box_t stdlib_print_string(box_t str, box_t world) {
    printf("%s", (char *) str);
    return world;
}

// believe_me
box_t believe_me(box_t a, box_t b, box_t v) {
    return v;
}

// sinter_crash
box_t sinter_crash() {
    exit(1);
    return NULL;
}

typedef struct {
    void *f;
    unsigned arity;
    unsigned args_so_far;
    box_t args[];
} closure_t;

// closure
box_t closure(box_t f, box_t arity_b) {
    unsigned arity = (unsigned) *arity_b;
    closure_t *c = gc_alloc(sizeof(closure_t) + (sizeof(box_t) * arity));
    c->f = (void *) f;
    c->arity = arity;
    c->args_so_far = 0;
    return (box_t) c;
}

box_t run_func(closure_t *c);

// closureApp
box_t closureApp(box_t cb, box_t arg) {
    closure_t *c = (closure_t *) cb;
    c->args[c->args_so_far] = arg;
    c->args_so_far++;

    if (c->args_so_far == c->arity) {
        return run_func(c);

    } else {
        return (box_t) c;
    }
}

#define _concat(a, b) a ## b
#define concat(a, b) _concat(a, b)

#define repeat_1(x) x
#define repeat_2(x) x, repeat_1(x)
#define repeat_3(x) x, repeat_2(x)
#define repeat_4(x) x, repeat_3(x)
#define repeat_5(x) x, repeat_4(x)
#define repeat_6(x) x, repeat_5(x)
#define repeat_7(x) x, repeat_6(x)
#define repeat_8(x) x, repeat_7(x)
#define repeat_9(x) x, repeat_8(x)
#define repeat_10(x) x, repeat_9(x)
#define repeat_11(x) x, repeat_10(x)
#define repeat_12(x) x, repeat_11(x)
#define repeat_13(x) x, repeat_12(x)
#define repeat_14(x) x, repeat_13(x)
#define repeat_15(x) x, repeat_14(x)
#define repeat_16(x) x, repeat_15(x)

#define repeat_n_1(x) concat(x, 1)
#define repeat_n_2(x) repeat_n_1(x), concat(x, 2)
#define repeat_n_3(x) repeat_n_2(x), concat(x, 3)
#define repeat_n_4(x) repeat_n_3(x), concat(x, 4)
#define repeat_n_5(x) repeat_n_4(x), concat(x, 5)
#define repeat_n_6(x) repeat_n_5(x), concat(x, 6)
#define repeat_n_7(x) repeat_n_6(x), concat(x, 7)
#define repeat_n_8(x) repeat_n_7(x), concat(x, 8)
#define repeat_n_9(x) repeat_n_8(x), concat(x, 9)
#define repeat_n_10(x) repeat_n_9(x), concat(x, 10)
#define repeat_n_11(x) repeat_n_10(x), concat(x, 11)
#define repeat_n_12(x) repeat_n_11(x), concat(x, 12)
#define repeat_n_13(x) repeat_n_12(x), concat(x, 13)
#define repeat_n_14(x) repeat_n_13(x), concat(x, 14)
#define repeat_n_15(x) repeat_n_14(x), concat(x, 15)
#define repeat_n_16(x) repeat_n_15(x), concat(x, 16)

#define assign_arg(n, c, i) \
    concat(arg_, n) = c->args[i]; \
    i++

#define cast_apply_f(n, c) \
    return ((void *(*)(concat(repeat_, n)(void *))) c->f) \
        (concat(repeat_n_, n)(arg_))

#define new_case(n, c, i) \
    assign_arg(n, c, i); \
    if (c->arity == n) cast_apply_f(n, c)

box_t run_func(closure_t *c) {
    unsigned i = 0;

    box_t repeat_n_16(arg_);

    if (c->arity == 0) return ((void *(*)()) c->f)();
    new_case(1, c, i);
    new_case(2, c, i);
    new_case(3, c, i);
    new_case(4, c, i);
    new_case(5, c, i);
    new_case(6, c, i);
    new_case(7, c, i);
    new_case(8, c, i);
    new_case(9, c, i);
    new_case(10, c, i);
    new_case(11, c, i);
    new_case(12, c, i);
    new_case(13, c, i);
    new_case(14, c, i);
    new_case(15, c, i);
    new_case(16, c, i);

    assert(0);
}
