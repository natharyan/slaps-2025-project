//iterative factorial

function Fact(k: int): int
  decreases k
{
  if k <= 0 then 1 else k * Fact(k - 1)
}

method Factorial(n: int) returns (f: int)
    requires n >= 0
    ensures f == Fact(n)
{
    f := 1;
    var i := 1;

    while i <= n
        invariant 1 <= i <= n + 1
        invariant f == Fact(i - 1)
        decreases n - i
    {
        f := f * i;
        i := i + 1;
    }
}
