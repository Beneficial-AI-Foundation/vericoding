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
   var valid_elements: seq<int> := [];
   for i := 0 to |x| - 1
     invariant forall k :: 0 <= k < |valid_elements| ==> HasNoEvenDigit(valid_elements[k])
     invariant forall k :: 0 <= k < |valid_elements| ==> valid_elements[k] in x
     invariant forall k :: 0 <= k < i && HasNoEvenDigit(x[k]) && !(x[k] in valid_elements) ==> false // all HasNoEvenDigit elements seen so far ARE in valid_elements
   {
     if HasNoEvenDigit(x[i]) {
       var found := false;
       for j := 0 to |valid_elements| - 1
         invariant forall k :: 0 <= k < j ==> valid_elements[k] != x[i]
       {
         if valid_elements[j] == x[i] {
           found := true;
           break;
         }
       }
       if !found {
         valid_elements := valid_elements + [x[i]];
       }
     }
   }

   // Sort the unique valid elements
   for i := 0 to |valid_elements| - 2
     invariant forall k :: 0 <= k < i ==> valid_elements[k] <= valid_elements[k+1]
     invariant forall k :: 0 <= k < |valid_elements| ==> HasNoEvenDigit(valid_elements[k])
     invariant forall k :: 0 <= k < |valid_elements| ==> valid_elements[k] in x
     // This invariant helps to ensure elements remain within the original 'x'
     invariant forall e :: e in valid_elements ==> e in x
   {
     var minIdx := i;
     for j := i + 1 to |valid_elements| - 1
       invariant minIdx >= i
       invariant forall k :: i <= k < j ==> valid_elements[minIdx] <= valid_elements[k]
       invariant forall k :: 0 <= k < |valid_elements| ==> HasNoEvenDigit(valid_elements[k])
       invariant forall k :: 0 <= k < |valid_elements| ==> valid_elements[k] in x
       invariant forall e :: e in valid_elements ==> e in x
     {
       if valid_elements[j] < valid_elements[minIdx] {
         minIdx := j;
       }
     }
     if minIdx != i {
       var temp := valid_elements[i];
       valid_elements[i] := valid_elements[minIdx];
       valid_elements[minIdx] := temp;
     }
   }
   return valid_elements;
}
// </vc-code>

