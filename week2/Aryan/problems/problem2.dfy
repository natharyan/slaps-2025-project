// Problem 2: Integer Division (Quotient & Remainder)
// Write loop invariant(s) for this method

method IntegerDivision(dividend: int, divisor: int) returns (quotient: int, remainder: int)
    requires divisor > 0
    requires dividend >= 0 // constraint required for the condition remainder >= 0
    ensures dividend == divisor * quotient + remainder
    ensures 0 <= remainder < divisor
{
    quotient := 0;
    remainder := dividend;
    
    while remainder >= divisor
        invariant remainder == dividend - divisor * quotient
        invariant dividend >= remainder >= 0
        decreases remainder
    {
        quotient := quotient + 1;
        remainder := remainder - divisor;
    }
}

// Report: 
//  - added this constraint requires dividend >= 0 to ensure that remainder >= 0

// Output:
// Dafny program verifier finished with 1 verified, 0 errors