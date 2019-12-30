var x : int;

procedure m1(x: int) returns () //shadows global variable
    requires x > 0;
{
    assert x >= 0;    
}

procedure m2(y: int) returns ()
    requires y > 0;
{
    //var y: int; //error, not allowed to shadow param
}

procedure m3() returns ()
{
    var x: int; //shadows global variable
    x := 0; 
}
