import localsolver
import argparse
import matplotlib.pyplot as plt

parser = argparse.ArgumentParser()
parser.add_argument('-t', '--time', type=int, default=10) 
parser.add_argument('--orientations', type=str, required=True)
parser.add_argument('-p', '--precision', type=int, default=5, help='precision: 10^(-p)')
parser.add_argument('-x', '--x_ordering', action='store_true')
args = parser.parse_args()
time_limit = args.time
orientation_file = args.orientations
precision = args.precision
x_ordering = args.x_ordering
orientation_constraints = []
N = 0
EPSILON = 0.000025

with open(orientation_file, 'r', encoding='utf-8') as or_file:
    for line in or_file:
        orientation = line.split('_')[0]
        tokens = line.split('_')[1].replace("(", "").replace(")", "").replace(",", "").split(' ')
        nums = list(map(int, tokens))
        N = max(N, max(nums) + 1)
        def orientation_to_sign(orientation):
            if orientation == 'A':
                return 1
            elif orientation == 'B':
                return -1
            elif orientation == 'C':
                return 0
        orientation_constraints.append((*nums, orientation_to_sign(orientation)))

with localsolver.LocalSolver() as ls:
    #
    # Declare the optimization model
    #
    m = ls.model

    points = [(m.float(0, 20), m.float(0, 20)) for _ in range(N)]
    
    if x_ordering:
        for i in range(1, N-1):
            m.constraint(points[i][0] < points[i+1][0])
            
    # point 0 is the highest point
    for i in range(1, N):
        m.constraint(points[0][1] > points[i][1])

    gap_variables = []

    def builld_orientation_constraint(a, b, c, sign):
        determinant_exp = (c[1]-a[1])*(b[0]-a[0]) - (c[0] - a[0])*(b[1]-a[1])
        if sign == 1:
            m.constraint(determinant_exp > EPSILON)
        elif sign == -1:
            m.constraint(determinant_exp < -EPSILON)


    for or_constraint in orientation_constraints:
        a, b, c, sign = or_constraint
        a, b, c = points[a-1], points[b-1], points[c-1]
        builld_orientation_constraint(a, b, c, sign)

    t, l, r = points[0], points[1], points[N-1]
    area = t[0]*(l[1]- r[1])+ l[0]*(r[1]-t[1])+r[0]*(t[1]-l[1])
    
    l_2_separation_objective = m.min( (points[p1][0]-points[p2][0])*(points[p1][0]-points[p2][0]) + (points[p1][1]-points[p2][1])*(points[p1][1]-points[p2][1]) for p1 in range(N) for p2 in range(p1+1, N))
    # m.maximize(area)
    m.maximize(l_2_separation_objective)
    m.close()

    ls.param.time_limit = time_limit

    ls.solve()

    def p_value(point):
        return (point[0].value, point[1].value)

    for idx, point in enumerate(points):
        print(f"point #{idx}: {p_value(point)}")

    valued_points = list(map(p_value, points))
    x_coords, y_coords = zip(*valued_points)
    plt.scatter(x_coords, y_coords)
    plt.title(orientation_file)
    plt.savefig(f"{orientation_file}.png")
