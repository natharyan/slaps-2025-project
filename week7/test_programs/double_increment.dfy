// Test program: Two variables incrementing together

method DoubleIncrement(n: int) returns (x: int, y: int)
  requires n >= 0
  ensures x == n
  ensures y == 2 * n
{
  x := 0;
  y := 0;
  
  while (x < n)
  {
    x := x + 1;
    y := y + 2;
  }
}
