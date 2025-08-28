try:
    try:
        print(10/0)
    except OSError as e:
        print('foo')
except ZeroDivisionError:
    print('div by zero')

try:
    with open('foo') as f:
        print(f)
except OSError:
    print('OSerror')
