#include <stdio.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>

typedef union {
  int32 i;
  float d;
} dbl;

value geti(value v) {
  dbl d;
  d.d = Double_val(v);
  return copy_int32(d.i);
}
