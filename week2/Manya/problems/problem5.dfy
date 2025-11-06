// Problem 5: Reversing a Number
// Write loop invariant(s) for this method

method ReverseNumber(n: int) returns (rev: int)
    requires n >= 0
    ensures rev == ReverseDigits(n)
{
    var orig := n;
    rev := 0;
    var num := n;
    
    while num > 0
        invariant num >= 0
        invariant ReverseDigits(orig) == rev * Power(10, NumDigits(num)) + ReverseDigits(num)
        decreases num
    {
        // if num >= 10{
            // assert ReverseDigits(num) == (num % 10) * Power(10, NumDigits(num) - 1) + ReverseDigits(num/10) by {ReverseDigitsDecomp(num); }
        // }
        var digit := num % 10;
        rev := rev * 10 + digit;
        num := num / 10;
    }
}

function ReverseDigits(n: int): int
  requires n >= 0
{
  if n == 0 then 0
  else (n % 10) * Power(10, NumDigits(n / 10)) + ReverseDigits(n / 10)
}

function NumDigits(n: int): (num: int)
  requires n >= 0
  ensures num >= 0
{
  if n == 0 then 0
  else if n < 10 then 1
  else 1 + NumDigits(n / 10)
}

// Helper function for power (needed for ReverseDigits)
function Power(base: int, exp: int): int
    requires exp >= 0
{
    if exp == 0 then 1 else base * Power(base, exp - 1)
}

// tried to solve for dafny verification but not fully correct 

