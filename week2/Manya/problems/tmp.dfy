// Helper lemma to prove properties about modulo operation
lemma ModuloLemma(a: int, b: int)
  requires a > 0 && b > 0
  ensures a % b >= 0
  ensures a % b < b
{
  // Dafny can prove this automatically
}

// Function to compute GCD with complete proof
function checkGCD(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures checkGCD(a, b) > 0
  // Additional ensures clauses to help with verification
  ensures b == 0 ==> checkGCD(a, b) == a
  ensures b > 0 ==> checkGCD(a, b) == checkGCD(b, a % b)
  decreases b
{
  if b == 0 then 
    a 
  else (
    // Help Dafny understand that a % b satisfies the preconditions
    assert b > 0;
    ModuloLemma(a, b);
    assert a % b >= 0;
    assert a % b < b;
    checkGCD(b, a % b)
  )
}

// Method version with explicit proof steps
method ComputeGCD(a: int, b: int) returns (result: int)
  requires a > 0 && b >= 0
  ensures result > 0
  ensures result == checkGCD(a, b)
{
  var x := a;
  var y := b;
  
  while y != 0
    invariant x > 0 && y >= 0
    invariant checkGCD(x, y) == checkGCD(a, b)
    decreases y
  {
    ModuloLemma(x, y);
    var temp := x % y;
    x := y;
    y := temp;
  }
  
  result := x;
  
  // Final assertion to help verification
  assert y == 0;
  assert result == x;
  assert checkGCD(x, 0) == x;
}


// Theorem: GCD will yield a common divisor
lemma GCDDividesBoth(a: int, b: int)
  requires a > 0 && b >= 0
  ensures a % checkGCD(a, b) == 0
  ensures b > 0 ==>  b % checkGCD(a, b) == 0
  decreases b
{
  if b == 0 {
    assert checkGCD(a, b) == a;
    assert a % a == 0;
  } else {
    
  }
}