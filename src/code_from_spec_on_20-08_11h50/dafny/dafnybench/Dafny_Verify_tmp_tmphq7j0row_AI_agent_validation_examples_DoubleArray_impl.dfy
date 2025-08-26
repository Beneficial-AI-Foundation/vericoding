method DoubleArray(src: array<int>, dst: array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
// </vc-spec>
// <vc-code>
{
    var n := 0;
    while n != src.Length
        invariant 0 <= n <= src.Length
        invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
    {
        dst[n] := 2 * src[n];
        n := n + 1;
    }
}
// </vc-code>

// Original davinci-003 completion:
// method DoubleArray(src: array<int>, dst: array<int>)
//     requires src.Length == dst.Length
//     modifies dst
//     ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
// {
//     var n := 0;
//     var i : int := 0;
//     while n != src.Length
//     {
//         dst[n] := 2 * src[n];
//         n := n + 1;
//         i := i + 1;
//     } 
//     assert i == src.Length;
// }

// Fine_tuned davinci-003 completion:
// method DoubleArray1(src: array<int>, dst: array<int>)
//     requires src.Length == dst.Length
//     modifies dst
//     ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
// {
//     var n := 0;
//     while n != src.Length
//         invariant 0 <= n <= src.Length
//         invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
//     {
//         dst[n] := 2 * src[n]; n := n + 1;
//     }
// }


// Original davinci-003 completion:
// method RotateLeft(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)]) 
//     ensures a[a.Length -1] == old(a[0])
// {
//     var n := 0;
//     // loop invariant: forall i :: 0 <= i < n ==> a[i] == old(a[(i+1)])
//     while n != a.Length - 1
//     {
//         a[n], a[n+1] := a[n+1], a[n];
//         n := n + 1; 
//     }
// }

// Fine_tuned davinci-003 completion:
// method RotateLeft1(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)])
//     ensures a[a.Length -1] == old(a[0])
// {
//     var n := 0;
//     while n != a.Length - 1
//         invariant 0 <= n <= a.Length - 1
//         invariant forall i :: 0 <= i < n ==> a[i] == old(a[(i+1)])
//         invariant forall i :: 0 <= i < a.Length - 1 ==> a[i] == old(a[(i+1)])
//     {
//         a[n], a[n+1] := a[n+1], a[n];
//         n := n + 1;
//     }
// }


// Original davinci-003 completion:
// method RotateRight(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)]) 
//     ensures a[0] == old(a[a.Length-1])
// {
//     var n := 1;
//     var temp := a[0];
//     while n != a.Length
//     {
//         a[0] := a[n];
//         a[n] := temp;
//         temp := a[0];
//         n := n + 1;
//         // loop invariant:
//         // forall k :: 0 <= k < n ==> a[k] == old(a[k+1])
//     } 
// }

// Fine_tuned davinci-003 completion:
// method RotateRight1(a: array)
//     requires a.Length > 0
//     modifies a
//     ensures forall i :: 1<= i < a.Length ==> a[i] == old(a[(i-1)])
//     ensures a[0] == old(a[a.Length-1])
// {
//     var n := 1;
//     while n != a.Length
//         invariant 1 <= n <= a.Length
//         invariant forall i :: 1<= i < n ==> a[i] == old(a[(i-1)])
//         invariant forall i :: 1<= i < a.Length ==> a[i] == old(a[i])
//     {
//         a[0], a[n] := a[n], a[0]; n := n + 1;
//     }
// }