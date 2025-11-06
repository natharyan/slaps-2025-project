//count number of digits in a number

method CountDigits(n: int) returns (count: int)
    requires n > 0
    ensures count == NumDigits(n)
{
    count := 0;
    var num := n;

    while num > 0
        invariant num >= 0
        invariant n >= num
        invariant count + (if num > 0 then NumDigits(num) else 0) == NumDigits(n)
        decreases num
    {
        num := num / 10;
        count := count + 1;
    }
}

function NumDigits(n: int): int
    requires n > 0
{
    if n < 10 then 1 else 1 + NumDigits(n / 10)
}
