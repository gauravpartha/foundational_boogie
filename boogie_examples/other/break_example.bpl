procedure p() {
    var y : int;

    y := 0;
    while (true)
        invariant true;
    {
        y := y + 1;
	if(y > 1)
	{
            break;
	}
    }

    assert y >= 0;
}
