ensures forall k, l :: 0 <= k < l < evenNumbers.Length ==>
              exists n, m :: 0 <= n < m < arr.Length && evenNumbers[k] == arr[n] && evenNumbers[l] == arr[m]