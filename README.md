# ASk: Alex' Skolemizer

```
usage: ask [OPTIONS] <file with one formula> [<output file>]

 Apply a Skolemization transformation to the input file.
 It is assumed that bound variables are named apart, and that there are no free variables.
 <file with one formula> can be either a file name or '-' (without parentheses) for stdin.
 If <output file> is specified, write result to <output file>, otherwise to stdout.

 If no options are provided, all the existentials in the formula are Skolemized,
 using some fixed symbol suffixed with _NN, NN=00-99.
 
 If only -s is provided and <Skolem symbol to use> is of the form
 <something>_NN, Skolemize all the existentials in the formula, using
 the symbol <something> replacing NN with 00-99.
 
 If only -s is provided and <Skolem symbol to use> is not of the form
 <something>_NN, Skolemize the leftmost existentially quantified variable
 in the formula, using the <Skolem symbol to use>.
 
 If only -v is provided, Skolemize the <variable to Skolemize>, using
 some fixed symbol suffixed with _00.
 
 If both -s and -v are provided, Skolemize the <variable to Skolemize> using
 the symbol <Skolem symbol to use>.

 If -e is specified, also output the equality between the Skolem term and
   an epsilon term.

Options:
  -v <variable to Skolemize>
     The existential variable to Skolemize.

  -s <Skolem symbol to use>
     The Skolem symbol base name to use for the Skolemization symbols.
     Defaults to "aSk" if omitted.
     
  -e Output a choice term for the Skolem term.

  --no-tstp
     Disable TSTP-compatible output: The output in <output file> (or stdout) will
     not start with a SZS status value and the output will not be wrapped within
     SZS BEGIN and SZS END block delimiters.

  --version
     Prints the version number of the executable and terminates.

  --help
     Prints this description and terminates.```
