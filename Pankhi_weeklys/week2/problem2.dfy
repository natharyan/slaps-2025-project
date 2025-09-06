// Problem 2: Integer Division (Quotient & Remainder)
// Write loop invariant(s) for this method

method IntegerDivision(dividend: int, divisor: int) returns (quotient: int, remainder: int)
    requires divisor > 0
    requires dividend > 0 
// ^^ added to prevent r from being initialised as negative
    ensures dividend == divisor * quotient + remainder
    ensures 0 <= remainder < divisor
{
    quotient := 0;
    remainder := dividend; // could be negative? but not allowed
    
    while remainder >= divisor
        // TODO: Write loop invariant(s)
        invariant dividend == divisor * quotient + remainder
        invariant 0<= quotient<= dividend/divisor 
        invariant dividend >= remainder >= 0
        decreases remainder
    {
        quotient := quotient + 1;
        remainder := remainder - divisor;
    }
}