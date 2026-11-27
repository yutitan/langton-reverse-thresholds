"""朗顿蚂蚁：严格验证给定有限初态、指定时刻以后的 104 步平移周期。

用 Python 3 直接运行即可核验全白棋盘和一个可以任意推迟的干扰。
坐标向东、向北为正。t=0 表示任何一步之前，朝北，白格右转。

若第一个块读到的格集合为 P，位移是 v，B0、B1 分别是块首、块尾的
黑格集，令 D 为 B1 与 B0+v 的对称差。若块首尾朝向相同且 v 非零，
反复平移这一块的充要条件是 D 不交所有 P+j*v（j 为正整数）。
证明：对比实际的块尾状态与平移 v 后的块首状态，两者头部相同。
只要未触及 D，它们读色和翻色完全相同，棋盘的差集恒为 D。条件保证
第二块照第一块平移；逐块归纳，实际轨迹始终比其平移副本提前一块。
反之，若处处重复，两个轨迹永远同步，第一次读到差异格会导致相反的
转向，故所有将读的格均在 D 以外。该检查只对传入的初态和时刻作判断。
"""

from dataclasses import dataclass

VECTORS = ((0, 1), (1, 0), (0, -1), (-1, 0))
PERIOD = 104


@dataclass
class Ant:
    black: set
    x: int = 0
    y: int = 0
    heading: int = 0

    def step(self):
        point = (self.x, self.y)
        left = point in self.black
        if left:
            self.black.remove(point)
        else:
            self.black.add(point)
        self.heading = (self.heading + (-1 if left else 1)) % 4
        dx, dy = VECTORS[self.heading]
        self.x += dx
        self.y += dy
        return "L" if left else "R"


def add(point, v, times=1):
    return point[0] + times*v[0], point[1] + times*v[1]


def positive_translate(p, q, v):
    """Whether q = p+j*v for an integer j >= 1, assuming v != (0,0)."""
    axis = 0 if v[0] else 1
    j, remainder = divmod(q[axis] - p[axis], v[axis])
    return remainder == 0 and j >= 1 and add(p, v, j) == q


def inspect_block(ant):
    """Advance one block. Test permanent repetition and return its local data."""
    start = (ant.x, ant.y)
    heading = ant.heading
    before = ant.black.copy()
    reads = []
    turns = []
    for _ in range(PERIOD):
        reads.append((ant.x, ant.y))
        turns.append(ant.step())
    v = ant.x-start[0], ant.y-start[1]
    if v == (0, 0) or ant.heading != heading:
        return False, v, reads, "".join(turns)
    diff = ant.black ^ {add(q, v) for q in before}
    points = set(reads)
    okay = not any(positive_translate(p, q, v) for p in points for q in diff)
    return okay, v, reads, "".join(turns)


def blank_demo():
    entry = 9977
    ant = Ant(set())
    prefix = set()
    for _ in range(entry):
        prefix.add((ant.x, ant.y))
        ant.step()
    okay, drift, reads, turns = inspect_block(ant)
    if not okay or tuple(map(abs, drift)) != (2, 2):
        raise AssertionError("Blank highway certificate rejected")
    if any(turns == turns[:d] * (PERIOD//d)
           for d in range(1, PERIOD) if PERIOD % d == 0):
        raise AssertionError("The turn word has a smaller period")
    print(f"t={entry}, drift={drift}, least turn period=104,"
          f" distinct reads={len(set(reads))}, R={turns.count('R')}, L={turns.count('L')}")

    # Take a point at the front of P; the same point shifted k*v cannot be
    # read in an earlier highway block. Pick k large enough to clear the prefix.
    front = max(set(reads), key=lambda q: (q[0]*drift[0]+q[1]*drift[1],q))
    first_phase = reads.index(front)
    k = 1000
    obstacle = add(front, drift, k)
    if obstacle in prefix:
        raise AssertionError("Obstacle overlaps the transient")
    when = entry + k*PERIOD + first_phase
    clean, altered = Ant(set()), Ant({obstacle})
    for t in range(when):
        if (clean.x,clean.y) == obstacle or clean.step() != altered.step():
            raise AssertionError(f"Unexpected early contact at t={t}")
    if (clean.x,clean.y) != obstacle or (altered.x,altered.y) != obstacle:
        raise AssertionError("Predicted first contact missed")
    clean_turn, changed_turn = clean.step(), altered.step()
    if clean_turn == changed_turn:
        raise AssertionError("Obstacle did not affect the turn")
    print(f"One initially black cell at {obstacle}: first differing turn is"
          f" update {when+1}, {clean_turn} vs {changed_turn}, after {k} entire blocks.")


if __name__ == "__main__":
    blank_demo()
