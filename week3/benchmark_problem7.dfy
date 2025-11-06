//sum of even numbers up to n

method SumEven(n: int) returns (res: int)
    requires n >= 0
    ensures res == (n / 2) * ((n / 2) + 1)
{
    res := 0;
    var i := 0;

    while i <= n
        invariant 0 <= i <= n + 1
        invariant res == (if i == 0 then 0 else ((i - 1) / 2) * (((i - 1) / 2) + 1))
        decreases n - i
    {
        if i % 2 == 0 {
            res := res + i;
        }
        i := i + 1;
    }
    assert i == n + 1;
    assert res == (n / 2) * ((n / 2) + 1);

}
