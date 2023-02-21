521030910331 梁亚伦 <liangyalun@sjtu.edu.cn>

1\. (\f n. f (f (f n))) (\f x. f (x + 1)) (\x. x) 0
= (\n. (\z. (\y. (\x. n (x + 1)) (y + 1)) (z + 1))) (\x. x) 0
= (\n. (\z. n (z + 3))) (\x. x) 0
= (\z. (z + 3)) 0
= 3.

2\. (\f n. f (f (f n))) (\f x. f (x + 1)) (\x. x - 2) 0
= (\n. (\z. n (z + 3))) (\x. x - 2) 0
= (\z. (z + 3) - 2) 0
= 1.

3\. (\f n. f (f (f n))) (\f x. f (x + 1)) (\x. x * x) 0
= (\n. (\z. n (z + 3))) (\x. x * x) 0
= (\z. (z + 3) * (z + 3)) 0
= 9.

4\. (\f g x. f (g x)) (\x. x - 2) (\x. x * x) 10
= (\g x. (g x) - 2) (\x. x * x) 10
= (\x. x * x - 2) 10
= 98.

5\. (\f g x. f (g x)) (\x. x * x) (\x. x - 2) 10
= (\g x. (g x) * (g x)) (\x. x - 2) 10
= (\x. (x - 2) * (x - 2)) 10
= 64.

6\. (\f n. f (f (f n))) (\f x y. f y x) = \f x y. f y x.
(\f x y. f y x) (\f g x. f (g x)) = \f g x. g (f x).
(\f g x. g (f x)) (\x. x * x) = \g x. g (x * x).
(\g x. g (x * x)) (\x. x - 2) = \x. (x * x) - 2.
(\x. (x * x) - 2) 10 = 98.
