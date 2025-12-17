// Test program: Simple counter loop without invariants

method Counter(n: int) returns (count: int)
  requires n >= 0
  ensures count == n
{
  var i := 0;
  count := 0;
  
  while (i < n)
  {
    count := count + 1;
    i := i + 1;
  }
}
