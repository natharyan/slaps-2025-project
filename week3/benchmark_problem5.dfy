//check if a sequence is a palindrome

function rev<T>(s: seq<T>): seq<T>
    decreases |s|
{
    if |s| == 0 then [] else rev(s[1..]) + [s[0]]
}
lemma revConcat<T>(x: seq<T>, y: seq<T>)
    decreases |x|
    ensures rev(x + y) == rev(y) + rev(x)
{
    if |x| == 0 {
        assert x == [];
        assert x + y == y;
        assert rev(x + y) == rev(y);
        assert rev(x) == [];
        assert rev(y) + rev(x) == rev(y) + [];
        assert rev(y) + [] == rev(y);
    } else {
        var x0 := x[0];
        var xs := x[1..];
        assert x == [x0] + xs;
        assert x + y == [x0] + xs + y;
        assert (x + y)[0] == x0;
        assert (x + y)[1..] == xs + y;
    assert rev(x + y) == rev((x + y)[1..]) + [(x + y)[0]];
        assert rev((x + y)[1..]) == rev(xs + y);
        assert rev(xs + y) == rev(y) + rev(xs);
        assert rev(x) == rev(xs) + [x0];
        assert rev(y) + rev(xs) + [x0] == rev(y) + rev(x);
        assert rev(x + y) == rev(y) + rev(x);
    }
}

method IsPalindrome(s: seq<char>) returns (res: bool)
    requires |s| >= 0
    ensures res <==> s == rev(s)
{
    var i := 0;
    var j := |s| - 1;
    res := true;

    while i < j
        invariant 0 <= i <= j + 1 <= |s|
        invariant res ==> s[..i] == rev(s[(j+1)..])
        decreases j - i
    {
        if s[i] != s[j] {
            res := false;
        } else {
            if res {
            assert s[i] == s[j];
            assert s[j..] == [s[j]] + s[(j+1)..];
            revConcat([s[j]], s[(j+1)..]);
            assert rev(s[j..]) == rev(s[(j+1)..]) + rev([s[j]]);
            assert rev([s[j]]) == [s[j]];
            assert s[..i+1] == s[..i] + [s[i]];
            assert s[..i] == rev(s[(j+1)..]);
            assert s[i] == s[j];
            assert rev(s[(j+1)..]) + [s[j]] == rev(s[(j+1)..]) + [s[i]];
            assert rev(s[(j+1)..]) + [s[i]] == s[..i] + [s[i]];
            assert rev(s[(j+1)..]) + [s[j]] == rev(s[j..]);
            assert s[..i+1] == rev(s[j..]);
            } else {
            }
        }

        i := i + 1;
        j := j - 1;
    }

    res := s == rev(s);
}