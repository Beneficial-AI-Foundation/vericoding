//IMPL
method IsArmstrong(n: int) returns (result: bool)
  requires 100 <= n < 1000
  ensures result <==> (n == ((n / 100) * (n / 100) * (n / 100) + ((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) + (n % 10) * (n % 10) * (n % 10)))
{
  var hundreds := n / 100;
  var tens := (n / 10) % 10;
  var ones := n % 10;
  
  var sumOfCubes := hundreds * hundreds * hundreds + tens * tens * tens + ones * ones * ones;
  
  result := n == sumOfCubes;
}