procedure return_in_loop() {
    var x: int;

    havoc x;
    while (x > 0)
    {
        x := x - 1;
        return;
    }

    while (x < 0)
        invariant x <= 0;
    {
        x := x + 1;
        return;
    }

    x := 0;
    assert x == 0;
}