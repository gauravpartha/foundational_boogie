procedure while_succ_in_while() {
    var x: int;
    var y: int;

    havoc x;
    havoc y;
    while (x > 0)
    {
        x := x - 1;
        while (y > 0)
        {
            y := y - 1;
        }
    }

    assert x == 0;
}