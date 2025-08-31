## Ensuring verification passes for the 3 examples:

1) dafny verify examples/example1.dfy

- Output:
Dafny program verifier finished with 2 verified, 0 errors

2) dafny verify examples/example2.dfy

- Output:
Dafny program verifier finished with 3 verified, 0 errors

3) dafny verify examples/example3.dfy

- Output: 
Dafny program verifier finished with 3 verified, 0 errors

## Output after modifying the ensures condition for example1.dfy

examples/example1.dfy(7,0): Error: a postcondition could not be proved on this return path
  |
7 | {
  | ^

examples/example1.dfy(6,16): Related location: this is the postcondition that could not be proved
  |
6 |     ensures sum < n * (n + 1) / 2
  |  


## Any issues encountered:

- No issues during the installation process or running the verification commands.