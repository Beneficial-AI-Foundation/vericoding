//SPEC
datatype arrays = arrayOne(arr1: array<real>) | arrayTwo(arr2: array2<real>) | arrayThree(arr3: array3<real>) 

//SPEC
method shape''(a: arrays) returns (ret: array<int>)
    ensures match a
              case arrayOne(arr1) => ret.Length == 1 && ret[0] == arr1.Length
              case arrayTwo(arr2) => ret.Length == 2 && ret[0] == arr2.Length0 && ret[1] == arr2.Length1
              case arrayThree(arr3) => ret.Length == 3 && ret[0] == arr3.Length0 && ret[1] == arr3.Length1 && ret[2] == arr3.Length2
{}


//SPEC
method shape(a: array2<real>) returns (ret: array<int>)
    ensures ret.Length == 2
    ensures ret[0] == a.Length0 && ret[1] == a.Length1;
{}
