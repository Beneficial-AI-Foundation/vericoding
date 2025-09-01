function HasNoEvenDigit(n: int) : bool
  decreases n
{
  n >= 0 && ((n < 10 && n % 2 == 1) || (n % 2 == 1 && HasNoEvenDigit(n / 10)))
}

// <vc-helpers>
function Digits(n: int): set<int>
  requires n >= 0
  decreases n
{
  if n < 10 then {n} else Digits(n / 10) + {n % 10}
}
// </vc-helpers>

// <vc-spec>
method UniqueDigits(x: seq<int>) returns (result: seq<int>)
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> HasNoEvenDigit(result[i])
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
  ensures forall e :: e in x && HasNoEvenDigit(e) ==> e in result
  ensures forall e :: e in result ==> e in x
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
   var valid_elements_set: set<int> := {};
   var valid_elements_list: seq<int> := [];

   for i := 0 to |x| - 1
     invariant forall k :: 0 <= k < |valid_elements_list| ==> HasNoEvenDigit(valid_elements_list[k])
     invariant forall k :: 0 <= k < |valid_elements_list| ==> valid_elements_list[k] in x
     invariant valid_elements_set == set valid_elements_list
     invariant forall k :: 0 <= k < i && HasNoEvenDigit(x[k]) ==> x[k] in valid_elements_set
   {
     if HasNoEvenDigit(x[i]) {
       if !(x[i] in valid_elements_set) {
         valid_elements_set := valid_elements_set + {x[i]};
         valid_elements_list := valid_elements_list + [x[i]];
       }
     }
   }

   // Sort the unique valid elements
   var list_as_array := new int[|valid_elements_list|];
   for i := 0 to |valid_elements_list| - 1 {
     list_as_array[i] := valid_elements_list[i];
   }

   for i := 0 to |list_as_array| - 2
     invariant forall k :: 0 <= k < i ==> list_as_array[k] <= list_as_array[k+1]
     invariant forall k :: 0 <= k < |list_as_array| ==> HasNoEvenDigit(list_as_array[k])
     invariant forall k :: 0 <= k < |list_as_array| ==> list_as_array[k] in x
     invariant list_as_array[i..] + list_as_array[..i] == valid_elements_list[..] // permutation
   {
     var minIdx := i;
     for j := i + 1 to |list_as_array| - 1
       invariant minIdx >= i
       invariant forall k :: i <= k < j ==> list_as_array[minIdx] <= list_as_array[k]
       invariant forall k :: 0 <= k < |list_as_array| ==> HasNoEvenDigit(list_as_array[k])
       invariant forall k :: 0 <= k < |list_as_array| ==> list_as_array[k] in x
       invariant list_as_array[i..] + list_as_array[..i] == valid_elements_list[..]
     {
       if list_as_array[j] < list_as_array[minIdx] {
         minIdx := j;
       }
     }
     if minIdx != i {
       var temp := list_as_array[i];
       list_as_array[i] := list_as_array[minIdx];
       list_as_array[minIdx] := temp;
     }
   }
   return list_as_array[..];
}
// </vc-code>

