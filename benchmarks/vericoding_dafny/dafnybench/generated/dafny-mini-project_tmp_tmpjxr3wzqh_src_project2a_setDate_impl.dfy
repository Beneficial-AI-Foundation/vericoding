// Define Date type
datatype Date = Date(year: int, month: int, day: int)

// Class containing the setDate method
class DateContainer {
    var date: Date
    
    constructor()
        ensures date == Date(0, 0, 0)
    {
        date := Date(0, 0, 0);
    }
    
    method setDate(d: Date)
        modifies this
        ensures date == d
    {
        date := d;
    }
}