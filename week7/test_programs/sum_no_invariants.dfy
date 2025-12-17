// Test program: Simple sum without invariants
// The pipeline should synthesize and insert invariants automatically

method Sum(n: int) returns (result: int)
  requires n >= 0
  ensures result == n * (n + 1) / 2
{
  var i := 0;
  var sum := 0;
  
  while (i <= n)
  {
    sum := sum + i;
    i := i + 1;
  }
  
  result := sum;
}
