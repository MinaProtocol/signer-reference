import random
import time

t = 3
s = 1
r = floor((t - s) / float(s))

#F = GF(prime)
#MS = MatrixSpace(F, t, t)

def print_matrix_format(M_int, n, t):
    print("n:", n)
    print("t:", t)
    print("N:", (n * t))
    hex_length = int(ceil(float(n) / 4)) + 2 # +2 for "0x"
    print("Prime number:", "0x" + hex(prime))
    print("MDS matrix (rows):")
    for i in range(0, t):
        print(["{0:#0{1}x}".format(entry, hex_length) for entry in M_int[i]])

def matrix_entries_to_int(M, t):
    M_int = []
    for i in range(0, t):
        M_int.append([])
        for j in range(0, t):
            M_int[i].append(int(M[i, j]))
    return M_int

def isAllInvertible(M, t):
    # Test all square submatrices for invertibility
    counter = 0
    all_invertible = True
    for i in range(2, t):
        choices_i = Combinations(range(0, t), i)
        for m in range(0, choices_i.cardinality()):
            for n in range(0, choices_i.cardinality()):
                M_sub = M[choices_i[m], choices_i[n]]
                is_inv = M_sub.is_invertible()
                all_invertible = all_invertible and is_inv
                #if is_inv == False:
                    #print("FALSE")
                    #print(M_sub)
                counter += 1
    #print("Submatrices checked:", counter)
    return all_invertible

def get_eigenvalues(mat):
    #print(mat.charpoly().roots())
    eigenvalues = [mat.charpoly().roots()[i][0] for i in range(0, len(mat.charpoly().roots()))]
    return eigenvalues

def get_eigenvectors(mat):
    # Computing the right eigenvectors
    eigenvalues = get_eigenvalues(mat)
    eigenvectors = []
    for i in range(0, len(eigenvalues)):
        #print(eigenvalues[i])
        eig_basis = ((mat - eigenvalues[i] * matrix.identity(F, t)).right_kernel()).basis()
        for vec in eig_basis:
            eigenvectors.append(vec)
    return eigenvectors

def generate_vectorspace(round_num, M, M_round):
    V = VectorSpace(F, t)
    if round_num == 0:
        return V
    elif round_num == 1:
        return V.subspace(V.basis()[s:])
    else:
        mat_temp = matrix(F)
        for i in range(0, round_num-1):
            add_rows = []
            for j in range(0, s):
                add_rows.append(M_round[i].rows()[j][s:])
            mat_temp = matrix(mat_temp.rows() + add_rows)
        r_k = mat_temp.right_kernel()
        extended_basis_vectors = []
        for vec in r_k.basis():
            extended_basis_vectors.append(vector([0]*s + list(vec)))
        S = V.subspace(extended_basis_vectors)

        return S

def subspace_times_matrix(F, subspace, M):
    V = VectorSpace(F, t)
    subspace_basis = subspace.basis()
    new_basis = []
    for vec in subspace_basis:
        new_basis.append(M * vec)
    new_subspace = V.subspace(new_basis)
    return new_subspace

# Returns True if the matrix is considered secure, False otherwise
def algorithm_1(F, M):
    R.<x> = PolynomialRing(F)
    decomposition = M.minimal_polynomial().squarefree_decomposition()

    # Get A's
    V = VectorSpace(F, t)
    unit_vector_space = V.subspace(V.basis()[s:])
    A_list = []
    basis_vectors = []
    for i in range(0, len(list(decomposition))):
        poly = list(decomposition)[i][0]
        exponent = list(decomposition)[i][1]
        A_i = R(poly^exponent)(M).right_kernel()
        A_list.append(A_i)

    basis_vectors = []
    for A_i in A_list:
        X_i = A_i.intersection(unit_vector_space)
        while X_i.dimension() > 0:
            X_i_new = X_i.intersection(subspace_times_matrix(F, X_i, M))
            if X_i == X_i_new:
                break
            X_i = X_i_new
        basis_vectors += X_i.basis()
    
    P_full_space = V.subspace(basis_vectors)
    if P_full_space.dimension() > 0:
        return [False, P_full_space]

    return [True, 0]

# Returns True if the matrix is considered secure, False otherwise
def algorithm_2(F, M):
    V = VectorSpace(F, t)
    trail = [None, None]
    test_next = False
    I = list(range(0, s))
    I_powerset = list(sage.misc.misc.powerset(I))[1:]
    for I_s in I_powerset:
        test_next = False
        new_basis = []
        for l in I_s:
            new_basis.append(V.basis()[l])
        IS = V.subspace(new_basis)
        for i in range(s, t):
            new_basis.append(V.basis()[i])
        full_iota_space = V.subspace(new_basis)
        for l in I_s:
            v = V.basis()[l]
            while True:
                delta = IS.dimension()
                v = M * v
                IS = V.subspace(IS.basis() + [v])
                if IS.dimension() == t or IS.intersection(full_iota_space) != IS:
                    test_next = True
                    break
                if IS.dimension() <= delta:
                    break
            if test_next == True:
                break
        if test_next == True:
            continue
        return [False, [IS, I_s]]

    return [True, None]

# Returns True if the matrix is considered secure, False otherwise
def algorithm_3(F, M):

    V = VectorSpace(F, t)
    l = 2*t
    r_limit = floor((t - s) / float(s))

    flag_secure = True
    subspaces_found = []

    # Generate round matrices
    M_round = []
    for j in range(0, l+1):
        M_round.append(M^(j+1))

    I = range(0, s)
    I_powerset = list(sage.misc.misc.powerset(I))[1:]

    for r in range(2, l+1):
        next_r = False
        for I_s in I_powerset:
            IS = None
            res_alg_2 = algorithm_2(F, M^r)
            if res_alg_2[1] == None:
                continue
            IS = res_alg_2[1][0]
            I_s = res_alg_2[1][1]

            if IS != None and IS.dimension() > 0:
                active_sbox_positions = [[] for _ in range(0, r)]
                active_sbox_positions[0] = I_s
                for j in range(1, r):
                    if IS == subspace_times_matrix(F, IS, M):
                        next_r = True
                        break
                    IS = subspace_times_matrix(F, IS, M)
                    for i in range(0, s):
                        # new_basis = [V.basis()[k] for k in range(0, t) if k != i]
                        new_basis = []
                        for k in range(0, t):
                            if k != i:
                                new_basis.append(V.basis()[k])
                        iota_space = V.subspace(new_basis)
                        if IS.intersection(iota_space) != IS:
                            single_iota_space = V.subspace([V.basis()[i]])
                            if IS.intersection(single_iota_space) == single_iota_space:
                                active_sbox_positions[j].append(i)
                            else:
                                next_r = True
                                break
                    if next_r == True:
                        break
                if next_r == True:
                    break
                if active_sbox_positions != [[] for _ in range(0, r)]:
                    flag_secure = False
                    subspaces_found.append([IS, r, active_sbox_positions])
        if next_r == True:
            continue
    
    return [flag_secure, subspaces_found]

def check_minpoly_condition(M):
    max_period = 2*t
    all_fulfilled = True
    M_temp = M
    for i in range(1, max_period + 1):
        if not ((M_temp.minimal_polynomial().degree() == t) and (M_temp.minimal_polynomial().is_irreducible() == True)):
            all_fulfilled = False
            break
        M_temp = M * M_temp
    return all_fulfilled

def construct_test_matrix_inv_active():

    M = None
    while M == None or M.is_invertible() == False:
        # New matrix
        M = matrix(F, t, t)

        # Random a, b, c, ...
        while M[1, 0] == F(0):
            M[1, 0] = F.random_element()
        for i in range(2, t):
            M[i, 0] = F.random_element()

        # Random M_{0,2}, M_{1,2}, ...
        for i in range(0, t):
            for j in range(2, t):
                M[i, j] = F.random_element()
        
        # Second column
        prod_sum = 1
        for i in range(2, t):
            prod_sum -= M[0, i]*M[i, 0]
        M[0, 1] = prod_sum/M[1, 0]
        for i in range(1, t):
            prod_sum = 0
            for j in range(2, t):
                prod_sum -= M[i, j]*M[j, 0]
            M[i, 1] = prod_sum/M[1, 0]

    return M

def construct_test_matrix_inv_active_gen():
    t_custom = 4
    M = None
    while M == None or M.is_invertible() == False:
        # New matrix
        M = matrix(F, t_custom, t_custom)

        # Random a, b, c, ...
        M[0, 0] = F(1)
        while M[1, 0] == F(0):
            M[1, 0] = F.random_element()
        for i in range(2, t_custom):
            M[i, 0] = F.random_element()

        # Random M_{0,2}, M_{1,2}, ...
        for i in range(0, t_custom):
            for j in range(2, t_custom):
                M[i, j] = F.random_element()
        
        # Second column
        prod_sum = 0
        for i in range(2, t_custom):
            prod_sum -= M[0, i]*M[i, 0]
        M[0, 1] = prod_sum/M[1, 0]
        for i in range(1, t_custom):
            prod_sum = -M[i, 0]
            for j in range(2, t_custom):
                prod_sum -= M[i, j]*M[j, 0]
            M[i, 1] = prod_sum/M[1, 0]

    return M

def construct_test_matrix_e2():
    t_custom = 8
    M = None
    while M == None or M.is_invertible() == False:
        # New matrix
        # Copy M_1 (CHANGE GLOBAL t)
        global t
        old_t = t
        t = 4
        M_1 = construct_test_matrix_521()
        t = old_t
        M = matrix(F, t_custom, t_custom)
        for i in range(0, 4):
            for j in range(0, 4):
                M[i,j] = M_1[i,j]

        # Construct M_2
        MS_reduced = MatrixSpace(F, 4, 4)
        M_2 = MS_reduced.random_element()
        for i in range(0, 4):
            M_2[i,0] = M_2[i,2]
            M_2[i,1] = M_2[i,3]
        for i in range(0, 4):
            for j in range(0, 4):
                M[i,j+4] = M_2[i,j]

        # Construct M_3
        M_3 = MS_reduced.random_element()
        for i in range(0, 4):
            M_3[i,0] = F(0)
            M_3[i,1] = -M_3[i,2] - M_3[i,3]
        for i in range(0, 4):
            for j in range(0, 4):
                M[i+4,j] = M_3[i,j]

        # Construct M_4 (circ(a, b, c, d) with two eigenvalues)
        init_vec = vector([F.random_element() for _ in range(0, 4)])
        M_4 = matrix.circulant(init_vec)
        while len(get_eigenvalues(M_4)) != 2:
            init_vec = vector([F.random_element() for _ in range(0, 4)])
            M_4 = matrix.circulant(init_vec)
        for i in range(0, 4):
            for j in range(0, 4):
                M[i+4,j+4] = M_4[i,j]
    
    return M
