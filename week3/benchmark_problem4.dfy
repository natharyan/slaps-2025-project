//binary search

//function that returns true if key is present in sorted array a
method BinarySearch(a: array<int>, key: int) returns (found: bool)
    requires a != null && a.Length >= 0
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    ensures found <==> exists i :: 0 <= i < a.Length && a[i] == key
{
    var low := 0;
    var high := a.Length - 1;
    found := false;

    while low <= high
        invariant (0 <= low && high < a.Length) || a.Length == 0
    invariant forall i :: 0 <= i < low && i < a.Length ==> a[i] < key
    invariant forall i :: high < i < a.Length && i >= 0 ==> a[i] > key
        decreases high - low
    {
        var mid := (low + high) / 2;
        if a[mid] == key {
            found := true;
            return;
        } else if a[mid] < key {
            low := mid + 1;
        } else {
            high := mid - 1;
        }
    }
}
