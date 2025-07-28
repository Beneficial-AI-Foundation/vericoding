/* code modified by LLM (iteration 1): Added complete method signature for the incomplete code fragment at the beginning */
method LinearSearchBasic(a: array<int>, target: int) returns (n: int)
    requires a != null
    ensures -1 <= n < a.Length
    ensures n == -1 || a[n] == target
    ensures n != -1 ==> forall i :: 0 <= i < n ==> a[i] != target
    ensures n == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != target
{
    var i := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] != target
    {
        if a[i] == target {
            return i;
        }
        i := i + 1;
    }
    return -1;
}

//ATOM
method LinearSearch1Int(a: array<int>, target: int, s1_len: int) returns (n: int)
    requires a != null
    requires 0 <= s1_len <= a.Length
    ensures -1 <= n < a.Length
    ensures n == -1 || a[n] == target
    ensures n != -1 ==> forall i :: 0 <= i < n ==> a[i] != target
    ensures n == -1 ==> forall i :: 0 <= i < s1_len ==> a[i] != target
{
    var i := 0;
    while i < s1_len
        invariant 0 <= i <= s1_len
        invariant s1_len <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] != target
    {
        if a[i] == target {
            return i;
        }
        i := i + 1;
    }
    return -1;
}

//ATOM
method LinearSearch2Int(data: array<int>, element: int, s1_len: int) returns (position: int)
    requires data != null
    requires 0 <= s1_len <= data.Length
    ensures position == -1 || position >= 1
    ensures position >= 1 ==> exists i :: 0 <= i < s1_len && data[i] == element
    ensures position == -1 ==> forall i :: 0 <= i < s1_len ==> data[i] != element
{
    if s1_len == 0 {
        return -1;
    }
    
    var i := s1_len - 1;
    while true
        invariant 0 <= i < s1_len
        invariant s1_len <= data.Length
        invariant s1_len > 0
        invariant forall j :: i < j < s1_len ==> data[j] != element
        decreases i + 1
    {
        if data[i] == element {
            return i + 1;
        }
        if i == 0 {
            break;
        }
        i := i - 1;
    }
    return -1;
}

//ATOM
method LinearSearch3Int(data: array<int>, element: int, s1_len: int) returns (position: int)
    requires data != null
    requires 0 <= s1_len <= data.Length
    ensures position == -1 || position >= 1
    ensures position >= 1 ==> s1_len != 0
{
    if s1_len == 0 {
        return -1;
    }
    
    var i := s1_len - 1;
    while true
        invariant 0 <= i < s1_len
        invariant s1_len <= data.Length
        invariant s1_len > 0
        decreases i + 1
    {
        if data[i] == element {
            return i + 1;
        }
        if i == 0 {
            break;
        }
        i := i - 1;
    }
    return -1;
}

/* code modified by LLM (iteration 1): Added main method to satisfy Dafny compilation requirements */
method Main()
{
    // Empty main method for compilation
}