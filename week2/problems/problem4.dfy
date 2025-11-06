// Problem 4: Fast Power (Exponentiation by Squaring)
// Write loop invariant(s) for this method

method FastPower(base: int, exp: int) returns (result: int)
    requires exp >= 0
    ensures result == Power(base, exp)
{
    var x := base;
    var n: nat := exp;
    result := 1;

    while n > 0
        invariant result * Power(x, n) == Power(base, exp)
        decreases n
    {
        if n % 2 == 1 {
            result := result * x;
        }
        Power_squaring(x, n);   // justify the invariant preservation
        x := x * x;
        n := n / 2;
    }
}

// Helper function (as you gave)
function Power(base: int, exp: int): int
  requires exp >= 0
{
  if exp == 0 then 1 else base * Power(base, exp - 1)
}

// Lemma: squaring identities for Power
lemma Power_squaring(b: int, n: nat)
  ensures (n % 2 == 0 ==> Power(b, n) == Power(b * b, n / 2))
  ensures (n % 2 == 1 ==> Power(b, n) == b * Power(b * b, n / 2))
  decreases n
{
  if n > 0 { Power_squaring(b, n - 1); }
}