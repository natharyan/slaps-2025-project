//summing elements of an array


//recursive function for computation 
function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + Sum(s[1..])
}

//adding the next element to a prefix increases the sum by that element 
lemma SumPrefixLemma(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures Sum(s[..k+1]) == Sum(s[..k]) + s[k]
{
  if k == 0 {
    assert Sum(s[..1]) == s[0];
    assert Sum(s[..0]) == 0;
  } else {
    assert Sum(s[..k+1]) == s[0] + Sum(s[1..k+1]);
    assert Sum(s[..k]) == s[0] + Sum(s[1..k]);
    var s1 := s[1..];
    SumPrefixLemma(s1, k-1);
    assert s1[k-1] == s[k];
    assert s1[..(k-1)+1] == s[1..k+1];
    assert s1[..(k-1)] == s[1..k];
    assert Sum(s[1..k+1]) == Sum(s[1..k]) + s[k];
  }
}

method ArraySum(a: array<int>) returns (sum: int)
  ensures sum == Sum(a[..])
{
    sum := 0;
    var i := 0;

  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant sum == Sum(a[..i])
    decreases a.Length - i
  {
    SumPrefixLemma(a[..], i);
    sum := sum + a[i];
    i := i + 1;
  }

  assert i == a.Length;
  assert a[..i] == a[..];
  assert sum == Sum(a[..]);
}
