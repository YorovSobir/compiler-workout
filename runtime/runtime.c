/* Runtime library */

# include <stdio.h>

/* Lread is an implementation of the "read" construct */
extern int read () {
  int result;

  printf ("> ");
  fflush (stdout);
  scanf  ("%d", &result);

  return result;
}

/* Lwrite is an implementation of the "write" construct */
extern int write (int n) {
  printf ("%d\n", n);
  fflush (stdout);

  return 0;
}
