// Problem 2: Integer Division (Quotient & Remainder)
// Write loop invariant(s) for this method

method IntegerDivision(dividend: int, divisor: int) returns (quotient: int, remainder: int)
    requires divisor > 0
    requires dividend >= 0 //added constraint for remainder >= 0 
    ensures dividend == divisor * quotient + remainder
    ensures 0 <= remainder < divisor
{
    quotient := 0;
    remainder := dividend;
    
    while remainder >= divisor
        // TODO: Write loop invariant(s)
        invariant remainder == dividend - divisor * quotient
        invariant quotient >= 0 
        invariant dividend >= remainder >= 0 
        decreases remainder
    {
        quotient := quotient + 1;
        remainder := remainder - divisor;
    }
}
