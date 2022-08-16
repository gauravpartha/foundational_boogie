procedure while_in_if_true() {
    var x: int;
    var y: int;

    havoc x;
    havoc y;
    if (x > 0)
    {

    }
    else
    {
        x := x - 1;
        while (y > 0)
        {
            y := y - 1;
        }
    }

    assert x < 0;
}