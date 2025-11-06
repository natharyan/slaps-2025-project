// Problem 4: Fast Power (Exponentiation by Squaring)
// Write loop invariant(s) for this method

method FastPower(base: int, exp: int) returns (result: int)
    requires exp >= 0
    ensures result == Power(base, exp)
{
    var x := base;
    var n := exp;
    result := 1;
    
    while n > 0
        // TODO: Write loop invariant(s)
        invariant n >= 0
        invariant Power(base, exp) == result * Power(x, n)
        decreases n
    {
        if n % 2 == 1 {
            // assert Power(x, n) == x * Power(x, n - 1) by { Power_OddExp(x, n); }
            result := result * x;
            n := n - 1;
        }
        else{ 
            // assert Power(x, n) == Power(x*x, n / 2) by { Power_EvenExp(x, n); }
            x := x * x;
            n := n / 2;
        }
    }
}

// Helper function
function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1 else base * Power(base, exp - 1)
}

// tried to solve for dafny verification 

// lemma {:axiom} Power_EvenExp(base: int, exp: int)
//     requires exp % 2 == 0 && exp >= 0 
//     ensures Power(base, exp) == Power(base * base, exp / 2)

// lemma {:axiom} Power_OddExp(base: int, exp: int)
//     requires exp % 2 == 1 && exp >= 0 
//     ensures Power(base, exp) == base * Power(base, exp - 1)