// Test program: Two variables incrementing together

method DoubleIncrement(n: int) returns (x: int, y: int)
  requires n >= 0
  ensures x == n
  ensures y == 2 * n
{
  x := 0;
  y := 0;
  
  while (x < n)
    invariant 0 <= x <= n
    invariant y == 2 * x
    invariant -n - x - y <= 0
  {
    x := x + 1;
    y := y + 2;
  }
}
