procedure if_inside_while() {
    var x: int;
    var y: int;

    havoc x;
    while (x > 0)
    {
        x := x - 1;
        if (x > 1)
        {
            y := 10;
        }
        else
        {
            y := 20;
        }
    }

    assert x == 0;
}