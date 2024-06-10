#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

//#define SBP
#define SIGNOTOPE

int orient (int a, int b, int c) {
  assert (a < b);
  assert (b < c);

  return a + (b-2)*(b-1)/2 + (c-3)*(c-2)*(c-1)/6;
}

int main (int argc, char** argv) {
  int n = atoi (argv[1]);

  int nVar = n * (n-1) * (n-2) / 6;                 // base variables
  int nCls = 0;
#ifdef SIGNOTOPE
  nCls += (n-3) * (n-2) * (n-1) * n / 3;            // signotope clauses
#endif
#ifdef SBP
  nCls += (n-1) * (n-2) / 2;                        // unit clauses
#endif
  nCls += n * (n-1) * (n-2) * (n-3) * (n-4) / 15;   // constraints

  printf ("p cnf %i %i\n", nVar, nCls);

#ifdef SBP
  // symmetry breaking predicate
  for (int c = 2; c <= n; c++)
    for (int b = 2; b < c; b++)
      printf ("%i 0\n", orient (1, b, c));
#endif
#ifdef SIGNOTOPE
  // single sign swap clauses
  for (int d = 1; d <= n; d++)
    for (int c = 1; c < d; c++)
      for (int b = 1; b < c; b++)
        for (int a = 1; a < b; a++) {
          printf ("%i %i %i 0\n",  orient (a, b, c), -orient (a, b, d),  orient (a, c, d));
          printf ("%i %i %i 0\n", -orient (a, b, c),  orient (a, b, d), -orient (a, c, d));
          printf ("%i %i %i 0\n",  orient (a, b, c), -orient (a, b, d),  orient (b, c, d));
          printf ("%i %i %i 0\n", -orient (a, b, c),  orient (a, b, d), -orient (b, c, d));
          printf ("%i %i %i 0\n",  orient (a, b, c), -orient (a, c, d),  orient (b, c, d));
          printf ("%i %i %i 0\n", -orient (a, b, c),  orient (a, c, d), -orient (b, c, d));
          printf ("%i %i %i 0\n",  orient (a, b, d), -orient (a, c, d),  orient (b, c, d));
          printf ("%i %i %i 0\n", -orient (a, b, d),  orient (a, c, d), -orient (b, c, d)); }
#endif

  // print constraints
  for (int a = 1; a <= n; a++)
    for (int b = a + 1; b <= n; b++)
      for (int c = b + 1; c <= n; c++)
        for (int d = c + 1; d <= n; d++)
          for (int e = d + 1; e <= n; e++) {
            printf ("%i %i %i 0\n",  orient(a, b, c),  orient (b, c, d),  orient (c, d, e));
            printf ("%i %i %i 0\n", -orient(a, b, c), -orient (b, c, d), -orient (c, d, e));
            printf ("%i %i %i 0\n",  orient(a, b, c),  orient (b, c, e), -orient (a, d, e));
            printf ("%i %i %i 0\n", -orient(a, b, c), -orient (b, c, e),  orient (a, d, e));
            printf ("%i %i %i 0\n",  orient(a, b, d),  orient (b, d, e), -orient (a, c, e));
            printf ("%i %i %i 0\n", -orient(a, b, d), -orient (b, d, e),  orient (a, c, e));
            printf ("%i %i %i 0\n",  orient(a, b, e), -orient (a, c, d), -orient (c, d, e));
            printf ("%i %i %i 0\n", -orient(a, b, e),  orient (a, c, d),  orient (c, d, e)); }
}
