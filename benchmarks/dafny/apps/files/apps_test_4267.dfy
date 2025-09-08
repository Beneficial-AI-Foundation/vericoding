Given a room temperature in degrees Celsius, determine whether to turn on an air conditioner.
The air conditioner should be turned on if and only if the temperature is 30°C or higher.

predicate ValidTemperature(temp: int)
{
    -40 <= temp <= 40
}

function ExpectedOutput(temp: int): string
{
    if temp >= 30 then "Yes\n" else "No\n"
}

predicate CorrectOutput(temp: int, output: string)
{
    output == ExpectedOutput(temp)
}

method solve(X: int) returns (result: string)
    requires ValidTemperature(X)
    ensures CorrectOutput(X, result)
{
    if X >= 30 {
        result := "Yes\n";
    } else {
        result := "No\n";
    }
}
