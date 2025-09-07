// Problem 3: GCD Calculation
// Write loop invariant(s) for this method
// lemma mods(a: int, b: int, x:int, y:int)
//     requires a > 0 && b > 0
//     requires (x == a && y ==b) || (x==b && y==
    
method GCD(a: int, b: int) returns (gcd: int)
    requires a > 0 && b > 0
    ensures gcd > 0 
    ensures a % gcd == 0 && b % gcd == 0 //
    ensures forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd 
{

    var x := a;
    var y := b;
    
    while y != 0
        // TODO: Write loop invariant(s)
        invariant (a>=b ==> x <= a) && (b>a ==> x <= b)
        invariant x > 0
        invariant 0 <= y <= b
        invariant forall d :: (d>0 && a % d == 0 && b % d == 0) ==> (x % d ==0 && y % d ==0)
        invariant (y==0) ==> (a % x == 0 && b % x == 0)
        decreases y
    {
        var temp := y;
        y := x % y;
        x := temp;
    }
    
    gcd := x;
}