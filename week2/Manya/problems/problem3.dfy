// Problem 3: GCD Calculation
// Write loop invariant(s) for this method

// everything commented out is not a part of the final submission, it's just present to show the thought process / rough work. 

// // helper function to compute GCD recursively
// function gcd(m: int, n: int): int
//     requires m > 0 && n >= 0
// {
//     if n == 0 then m else gcd(n, m % n)
// }

method GCD(a: int, b: int) returns (gcd: int)
    requires a > 0 && b > 0
    ensures gcd > 0
    ensures a % gcd == 0 && b % gcd == 0
    ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd
{
    var x := a;
    var y := b;
    
    while y != 0
        // TODO: Write loop invariant(s)
        invariant x > 0
        invariant y >= 0
        // invariant forall d :: d > 0 ==> (x % d == 0 && y % d == 0) <==> (a % d == 0 && b % d == 0) // this was not working 
        invariant forall d :: d > 0 && a % d == 0 && b % d == 0 ==> x % d == 0 && y % d == 0 
        // invariant gcd(x, y) == GCD // considered a gcd function but was getting too many errors and found a different solution 
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    
    gcd := x;
}


// got 1 time out: "problem3.dfy(11,7): Error: Verification of 'GCD' timed out after 30 seconds. (the limit can be increased using --verification-time-limit)" 