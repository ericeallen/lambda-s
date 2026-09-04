/*
Copyright (c) 2026 Eric Allen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Allen
*/
/* Numeric kernels for compiled Λs programs.

   The point of this file is what is *absent*. LambdaS.Map proves the units of a
   linear map are rank-one -- entry (j,i) carries dW(j)/dV(i) -- so an m-by-n map
   needs m+n units rather than m*n, and those live in the type, not the data. By
   the time control reaches here the checker has discharged every dimensional
   obligation, so the payload is a flat row-major array of doubles with no
   tagging, no strides and no per-entry metadata: exactly what BLAS expects.

   On Apple platforms that means the calls below go straight to Accelerate's
   cblas. Elsewhere the portable loops are used, so the build has no external
   dependency. */

#include <lean/lean.h>

#ifdef __APPLE__
/* Opt in to the non-deprecated CBLAS interface (macOS 13.3+). Without
   ACCELERATE_LAPACK_ILP64 the integer arguments stay 32-bit, matching the
   (int) casts below. */
#define ACCELERATE_NEW_LAPACK
#include <Accelerate/Accelerate.h>
#define LAMBDAS_HAVE_BLAS 1
#endif

/* y = A x, with A row-major m-by-n. One call per matrix-vector product. */
LEAN_EXPORT lean_object * lambdas_dgemv(b_lean_obj_arg m_, b_lean_obj_arg n_,
                                        b_lean_obj_arg a, b_lean_obj_arg x) {
    size_t m = lean_usize_of_nat(m_);
    size_t n = lean_usize_of_nat(n_);
    const double * A = lean_float_array_cptr(a);
    const double * X = lean_float_array_cptr(x);
    lean_object * res = lean_alloc_sarray(sizeof(double), m, m);
    double * Y = (double *)lean_sarray_cptr(res);
#ifdef LAMBDAS_HAVE_BLAS
    cblas_dgemv(CblasRowMajor, CblasNoTrans, (int)m, (int)n,
                1.0, A, (int)n, X, 1, 0.0, Y, 1);
#else
    for (size_t i = 0; i < m; i++) {
        double s = 0.0;
        const double * row = A + i * n;
        for (size_t j = 0; j < n; j++) s += row[j] * X[j];
        Y[i] = s;
    }
#endif
    return res;
}

/* Inner product of two flat vectors. */
LEAN_EXPORT double lambdas_ddot(b_lean_obj_arg a, b_lean_obj_arg x) {
    const double * A = lean_float_array_cptr(a);
    const double * X = lean_float_array_cptr(x);
    size_t na = lean_sarray_size(a);
    size_t nx = lean_sarray_size(x);
    size_t n = na < nx ? na : nx;
#ifdef LAMBDAS_HAVE_BLAS
    return cblas_ddot((int)n, A, 1, X, 1);
#else
    double s = 0.0;
    for (size_t i = 0; i < n; i++) s += A[i] * X[i];
    return s;
#endif
}

/* Which backend was compiled in, so a run can report it. */
LEAN_EXPORT lean_object * lambdas_blas_backend(lean_object * unit) {
    (void)unit;
#ifdef LAMBDAS_HAVE_BLAS
    return lean_mk_string("Accelerate cblas");
#else
    return lean_mk_string("portable C loop");
#endif
}
