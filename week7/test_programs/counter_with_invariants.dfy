// Test program: Simple counter loop without invariants

method Counter(n: int) returns (count: int)
  requires n >= 0
  ensures count == n
{
  var i := 0;
  count := 0;
  
  while (i < n)
    invariant 0 <= i <= n
    invariant count == i
    invariant -count - i - n <= 0
    invariant i >= 0
  {
    count := count + 1;
    i := i + 1;
  }
}
