procedure multi_assign_same_var() returns ()
{
    var i: int;
    i,i := 0,0; //illegal
}