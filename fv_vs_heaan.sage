from sage.stats.distributions.discrete_gaussian_integer import DiscreteGaussianDistributionIntegerSampler;
import copy
import os

#Parameter Setup
#polynomial ring
R.<y>=PolynomialRing(ZZ);

#supported schemes:
#FV: our variant of the FV scheme
#HEAAN: standard HEAAN with sparse secrets (h=128) and the special prime key switching
#HEAAN_FV_KS: HEAAN without sparse secrets and with the bit-decomposition key switching
sprtd_schemes = Set(['FV', 'HEAAN', 'HEAAN_FV_KS']);

#encryption parameters
#basic cyclotomic ring dimensions
ns = [2^11, 2^12, 2^13, 2^14, 2^15];
#ciphertext moduli to attain 128-bit security
qs = {
    'FV': [2^54, 2^109, 2^218, 2^438, 2^881],
    'HEAAN': [2^20, 2^41, 2^85, 2^171, 2^349],
    'HEAAN_FV_KS': [2^54, 2^109, 2^218, 2^438, 2^881]   
};

#discrete Gaussian distribution
#standard deviation of a gaussian distribution
st_dev = 3.19;
#discrete gaussian sampler
d_gauss = DiscreteGaussianDistributionIntegerSampler(st_dev);

def inf_norm(poly):
    '''Infinity norm of a polynomial
    Parameters:
        poly (in R<y>): polynomial

    Returns:
        res (in ZZ): the infinity norm of the given polynomial
    '''
    if not (poly in R):
        raise TypeError("Input must be a polynomial in ZZ<y>");

    if poly == R(0):
        return 0;

    res = max([max(poly), abs(min(poly))]);
    return res;

def balanced_expansion(inp, d, b, NAF=True):
    '''Expands the integer in base b

    Parameters:
        inp (int): integer to expand
        d (int): number of digits in the expansion
        b (int): expansion base
        NAF (bool): NAF encoding is turned on/off

    Returns:
        out (list of ints): integer expansion 
    '''
    if b < 2:
        raise ValueError("Expansion base can't be smaller than 2");

    d = ZZ(d);

    if inp == 0:
        return [0]*d;

    if b == 2:
        if (not NAF) and (ceil(log(abs(inp), b)) > d):
            raise ValueError("Input can't fit the given number of digits");

        if NAF and (ceil(log(abs(inp), b)) + 1 > d):
            raise ValueError("Input can't fit the given number of digits");
    else:
        if (b%2 == 1) and (inp > (b^d+1)/2 or inp < -(b^d - 1)/2):
            raise ValueError("Input can't fit the given number of digits");
        if (b%2 == 0) and (abs(inp) > b^d/2):
            raise ValueError("Input can't fit the given number of digits");

    sgn = 1;
    if inp < 0:
        sgn = -1;
        inp *= -1;
    if b == 2 and NAF: #NAF expansion
        out = [];
        i = 0;
        while inp > 0:
            if inp%2 == 1:
                zi = 2 - ZZ(inp%4);
                out += [sgn*zi];
                inp -= zi;
            else:
                out += [0];
            i += 1;
            inp /= 2;
        out += ([0]*(d - i));
        return out;
    elif b == 2: #binary expansion with sign
        out = [];
        for i in range(d):
            out += [sgn*ZZ(inp%2)];
            inp = ZZ((inp-ZZ(inp%2))/2);
        return out;
    elif b%2 == 0: #balanced base-b expansion with the sign when b is even
        out = [];
        carry = 0;
        for i in range(d):
            zi = ZZ(inp%b) + carry;
            inp = ZZ((inp - zi + carry)/b);
            if zi > b/2:
                zi -= b;
                carry = 1;
            else:
                carry = 0;
            out += [sgn*zi];
        return out;
    else: #balanced base-b expansion with the sign when b is odd
        if inp == (b^d+1)/2:
            out = [sgn*ZZ((b+1)/2)];
            for i in range(1,d):
                out += [sgn*ZZ((b-1)/2)];
            return out;
        else:
            out = [];
            for i in range(d-1):
                if ZZ(inp%b) > (b-1)/2:
                    out += [sgn*(ZZ(inp%b)-b)];
                    inp = ZZ((inp-ZZ(inp%b))/b)+1;
                else:
                    out += [sgn*ZZ(inp%b)];
                    inp = ZZ((inp-ZZ(inp%b))/b);
            if ZZ(inp%b) > (b-1)/2:
                out = [out[0]-sgn]+out[1:]+[sgn*(inp-b)];
            else:
                out += [sgn*inp];
            return out;

def bit_reverse(vec):
    '''Change the order of the vector elements by bit-reversing its indices

    Parameters:
        vec (array in CC): k-dimensional array of complex values

    Returns:
        res (array in CC): k-dimensional array of reversed complex values
    '''
    vec_len = len(vec);
    loglen = log(vec_len,2);

    if not (loglen in ZZ):
        raise ValueError('The vector length must be a power of 2');

    res = [0 for i in range(vec_len)];
    for i in range(vec_len):
        binary = bin(i);
        reverse = binary[-1:1:-1];
        reverse = reverse + (loglen-len(reverse))*'0';
        new_ind = int(reverse,2);
        res[i] = vec[new_ind];

    return res;

def get_b(n, slots, bit_bound):
    '''Return the base of a generalized Fermat prime b^(n/m)+1, where n is the ciphertext ring dimension and m is twice the number of cleartext slots. This prime should be bigger than a given bit-size bound. In addition, the base should be an mth power modulo b^(n/m)+1.

    Parameters:
        n: ring dimension
        slots: number of slots
        bit_bound: lower bound on a generalized Fermat prime
    '''
    m = 2*slots;
    k = n/m;
    if not (k in ZZ):
        raise ValueError("The number of slots should divide n");

    #find the minimal even integer to satisfy the given bound
    start = ZZ(ceil(2^(bit_bound/k)/2)*2);
    b = start;
    while True:
        p = ZZ(b^k + 1);
        if is_prime(p):
            try:
                mod(b,p).nth_root(m);
                break;
            except:
                pass;
        b+=2;

    return b;

def get_min_b(n, slots, bit_bound):
    '''Return the minimal base of a generalized Fermat prime b^(n/l)+1, where n is the ciphertext ring dimension and l is a multiple of m = 2*slots. This prime should be bigger than a given bit-size bound. In addition, the base should be an lth power modulo b^(n/l)+1.

    Parameters:
        n: ring dimension
        slots: number of slots
        bit_bound: lower bound on a generalized Fermat prime
    '''
    min_slots = slots;
    min_b = get_b(n, slots, bit_bound);

    alt_slots = 2*slots;
    while alt_slots != n/2:
        start = ZZ(ceil(2^(bit_bound/n*2*alt_slots)/2)*2);
        if start > min_b:
            break;
        alt_b = get_b(n,alt_slots,bit_bound);
        if alt_b < min_b:
            min_b = alt_b;
            min_slots = alt_slots;
        alt_slots*=2;

    print("Use {min_slots} slots with b={min_b}".format(min_slots=min_slots, min_b=min_b));
    return min_b;

##############PARAMS#######################
class Params:
    '''Encryption parameters'''

    def __init__(self, scheme_type, param_index):
        '''Constructor

        Parameters:
            scheme_type (str): scheme type ('FV'/'HEAAN'/'HEAAN_FV_KS')
            param_index (in ZZ): index of a parameter set
        '''
        if not scheme_type in sprtd_schemes:
            raise ValueError("This scheme is not supported"); 

        if not (param_index in ZZ) or (param_index < 0):
            raise ValueError("Params: Parameter index must be a non-negative integer");

        if param_index >= len(ns):
            raise ValueError("Params: Parameter index is too large, max");

        self.type = scheme_type; 

        #basic cyclotomic ring dimension
        self.n = ns[param_index];
        #ciphertext modulus
        self.q = qs[self.type][param_index];
        #decomposition base
        self.w = 2^32;
        #number of decomposition components
        self.l = floor(log(self.q, self.w));
        #standard deviation of a gaussian distribution
        #self.sigma = 3.19;
        #discrete gaussian sampler
        #self.D = DiscreteGaussianDistributionIntegerSampler(self.sigma)
        #indicates whether the plaintext parameters are initialized
        self.plain_init = False;

    def __str__(self):
        '''Returns a description of the class'''
        return "scheme: {stype}, n: {n}, q: {q}, w: {w}, l: {l}, st.dev: {sigma}".format(stype=self.type, n=self.n, q=self.q, w=self.w, l=self.l, sigma=st_dev);

    def __eq__(self, params):
        '''Equality test

        Parameters:
            params (Params): encryption parameters to compare with
        '''
        if not isinstance(params, Params):
            raise TypeError("Invalid parameters");

        if (self.type == params.type) and (self.n == params.n) and (self.q == params.q) and (self.w == params.w):
            return True;

        return False;

    def symred(self, num):
        '''Reduce the integer modulo the ciphertext modulus q within the symmetric interval

        Parameters:
            num (int): integer

        Returns:
            res (int): resulting integer 
        '''
        if not (num in ZZ):
            raise TypeError("Input must be an integer");

        half_q = self.q//2;
        if num > half_q or num <= -half_q:
            res = ZZ(num%self.q);
            if res > half_q:
                res -= self.q;
            return res;
        return num;

    def red(self, poly):
        '''Reduce coefficients of the polynomial modulo the ciphertext modulus q

        Parameters:
            pol (in R<y>): polynomial to reduce
        Returns:
            res (in R<y>): resulting polynomial   
        '''
        if not (poly in R):
            raise TypeError("Wrong polynomial");

        poll = list(poly);
        coef = [self.symred(poll[i]) for i in range(len(poll))];
        res = R(coef);
        return res;

    def set_ptxt_params(self, m, b=None):
        '''Generate plaintext parameters

        Parameters:
            m (int): plaintext space dimension
            b (int): constant term of the plaintext polynomial (only for FV)
        '''
        if not (m in ZZ):
            raise TypeError("m is not an integer");
        if m == 0:
            raise NotImplementedError("m must be a positive number");
        if self.n%m != 0:
            raise ValueError("m must divide n");

        self.m = m;

        if self.type == 'FV':
            self.b = b;
            self.p = self.b^(self.n/self.m)+1;
            if self.m == 1:
                self.alpha = self.b;
            elif self.m <= 8 and self.b == 2^(m/2):
                #mth root of b modulo b^{n/m}+1
                self.alpha = (self.b^(self.n/(4*self.m))*(self.b^(self.n/(2*self.m))-1))%self.p;
            else:
                self.alpha = ZZ(mod(self.b, self.p).nth_root(self.m));
            
            #alpha^{-1}        
            self.beta = ZZ(mod(self.alpha,self.p)^(-1)); 

            self.g = RPoly(self, y^self.m + self.b);
            delta_coefs = [0 for _ in range(self.n)];
            for i in range(self.n/self.m):
                delta_coefs[self.n-(i+1)*self.m] = -ZZ(round(self.q/self.p*(-self.b)^i));
            self.Delta = RPoly(self, R(delta_coefs));
        
        self.plain_init = True;

    def set_mod(self, q):
        '''Set the ciphertext modulus q

        Parameters:
            q (in ZZ): new ciphertext modulus   
        ''' 

        if not (q in ZZ) or (q < 2):
            raise ValueError("Params: modulus must be an integer bigger than 2");

        if self.q != q:
            #ciphertext modulus
            self.q = q;
            #number of decomposition components
            self.l = floor(log(self.q, self.w));
            #indicates whether the plaintext parameters are initialized
            self.plain_init = False;
            if self.type == 'FV':
                self.set_ptxt_params(self.m, self.b);
            elif self.type == 'HEAAN' or self.type == 'HEAAN_FV_KS':
                self.set_ptxt_params(self.m);


##########CYCLOTOMIC INTEGERS#####################
class CyclInt:
    '''Cyclotomic integer'''

    def __init__(self, order, poly):
        '''Constructor

        Parameters:
            order (in ZZ): order of a cyclotomic field
            poly (in R<y>): polynomial representation of an element in the power basis
        '''
        if not(order in ZZ) or (order < 0):
            raise ValueError("CyclInt: The order must be a non-negative integer");
        if not(poly in R):
            raise TypeError("CyclInt: Incorrect polynomial");

        self.order = order;
        self.dim = euler_phi(order);
        self.mod = R(cyclotomic_polynomial(self.order))
        self.poly = poly%(self.mod);

    def __str__(self):
        '''Returns a description of the cyclotomic integer'''
        return str(self.poly);

    def __add__(self, cycl_int):
        '''Adds a cyclotomic integer to the current one

        Parameters:
            cycl_int (in R<y>): cyclotomic integer to add

        Returns:
            res (in R<y>): sum of two cyclotomic integers
        '''
        if not isinstance(cycl_int, CyclInt):
            raise ValueError("CyclInt: Wrong right addend");
        
        if self.order != cycl_int.order:
            raise ValueError("CyclInt: Different orders");

        res = CyclInt(self.order, self.poly + cycl_int.poly);
        return res;

    def __sub__(self, cycl_int):
        '''Subtracts a cyclotomic integer from the current one

        Parameters:
            cycl_int (in R<y>): cyclotomic integer to subtract

        Returns:
            res (in R<y>): difference of two cyclotomic integers
        '''
        if not isinstance(cycl_int, CyclInt):
            raise ValueError("CyclInt: Wrong right addend");
        
        if self.order != cycl_int.order:
            raise ValueError("CyclInt: Different orders");

        res = CyclInt(self.order, self.poly - cycl_int.poly);
        return res;

    def __mul__(self, cycl_int):
        '''Multiplies the current cyclotomic integer by another one

        Parameters:
            cycl_int (in R<y> or ZZ): cyclotomic integer to multiply

        Returns:
            res (in R<y>): product of two cyclotomic integers
        '''
        if isinstance(cycl_int, CyclInt):
            if self.order != cycl_int.order:
                raise ValueError("CyclInt: Different orders");
            res = CyclInt(self.order, ((self.poly * cycl_int.poly)%(self.mod)));
            return res;
        if cycl_int in ZZ:
            res = CyclInt(self.order, self.poly * cycl_int);
            return res;

        raise ValueError("CyclInt: Wrong right multiplicand");

    def scale_round(self, scale):
        '''Scale coefficient-wise and round

        Parameters:
            scale (in ZZ): integer whereby the polynomial coefficients should be scaled
        '''
        if not (scale in ZZ):
            raise TypeError("scale must be an integer");

        lst = list(self.poly);
        new_lst = [round(lst[i]/scale) for i in range(len(lst))];
        self.poly = R(new_lst);
    
###################POLYNOMIAL RING##################
class RPoly(CyclInt):
    '''Polynomial in the cyclotomic ring of integers R'''

    def __init__(self, params, poly):
        '''Standard constructor

        Parameters:
            params (Params): encryption parameters
            poly (in R<y>): polynomial representation of a polynomial in R
        '''
        if not isinstance(params, Params):
            raise TypeError("Parameters are invalid");
        if not (log(params.n, 2) in ZZ):
            raise NotImplementedError("Dimension must be a power of 2");

        self.params = params;
        CyclInt.__init__(self, 2 * params.n, poly);

    def __add__(self, rq_poly):
        '''Adds a polynomial to the current one

        Parameters:
            rq_poly (RPoly): polynomial in R to add

        Returns:
            res (poly in R<y>): sum of two polynomials
        '''
        if not isinstance(rq_poly, RPoly):
            raise TypeError("Wrong plaintext");
        if not (self.params == rq_poly.params):
            raise ValueError("Parameters must be equal");

        cycl = CyclInt.__add__(self, rq_poly);
        res = RPoly(self.params, cycl.poly);
        return res;

    def __sub__(self, rq_poly):
        '''Subtracts a polynomial to the current one

        Parameters:
            rq_poly (RPoly): polynomial in R to subtract

        Returns:
            res (poly in R<y>): difference of two polynomials
        '''
        if not isinstance(rq_poly, RPoly):
            raise TypeError("Wrong plaintext");
        if not (self.params == rq_poly.params):
            raise ValueError("Parameters must be equal");

        cycl = CyclInt.__sub__(self, rq_poly);
        res = RPoly(self.params, cycl.poly);
        return res;

    def __mul__(self, rq_poly):
        '''Multiplies a polynomial by the current one

        Parameters:
            rq_poly (RPoly or ZZ): polynomial or integer to multiply

        Returns:
            res (poly in R<y>): product of two polynomials
        '''

        if isinstance(rq_poly, RPoly):        
            if not (self.params == rq_poly.params):
                raise ValueError("Parameters must be equal");

            cycl = CyclInt.__mul__(self, rq_poly);
            res = RPoly(self.params, cycl.poly);
            return res;
        if rq_poly in ZZ:
            cycl = CyclInt.__mul__(self, rq_poly);
            res = RPoly(self.params, cycl.poly);
            return res;

        raise TypeError("Wrong plaintext");

    def __neg__(self):
        '''Negation of the current polynomial
        
        Returns:
            res (RPoly): negated polynomial
        '''
        res = RPoly(self.params, -self.poly);
        return res;

    def __eq__(self, rpoly):
        '''Checks whether a given poly is equal to the current one

        Parameters:
            rpoly (RPoly): polynomial to compare with

        Returns:
            res (bool): True if the given poly is equal to the current one, False otherwise
        '''

        if not isinstance(rpoly, RPoly):
            raise TypeError("Right-hand side argument must be RPoly");

        res = (self.poly == rpoly.poly) and (self.params == rpoly.params);
        return res; 

    def scale_round(self, scale):
        '''Scale coefficient-wise and round

        Parameters:
            scale (in ZZ): integer whereby the polynomial coefficients should be scaled
        '''
        if not (scale in ZZ):
            raise TypeError("scale must be an integer");

        lst = list(self.poly);
        new_lst = [round(lst[i]/scale) for i in range(len(lst))];
        self.poly = R(new_lst);

    def inf_norm(self):
        '''Infinity norm

        Returns:
            res (in ZZ): infinity norm of the current polynomial
        '''
        return inf_norm(self.poly);

    def hamming_weight(self):
        '''Hamming weight

        Returns:
            res (in ZZ): Hamming weight of the current polynomial
        '''
        return self.poly.hamming_weight();

    def modq(self):
        '''Reduction modulo the ciphertext modulus'''
        self.poly = self.params.red(self.poly);

    def mod_poly(self, rpoly):
        '''Reduces the current polynomial modulo a given polynomial
        
        Parameters:
            poly (RPoly): polynomial modulus
        '''
        if not isinstance(rpoly, RPoly):
            raise TypeError("Input must be RPoly");
        if rpoly.poly == R(0):
            raise ValueError("Zero-input is not allowed");

        self.poly = self.poly%(rpoly.poly);

    def modt(self):
        '''Reduction modulo the plaintext modulus'''
        if not self.params.plain_init:
            raise ValueError("Plaintext space must be initialized");

        if self.params.type == 'HEAAN' or self.params.type == 'HEAAN_FV_KS':
            print("There is no plaintext modulus in HEAAN");
        elif self.params.type == 'FV':
            self.mod_poly(self.params.g);

#################GENERATOR OF RANDOM POLYNOMIALS###############

class RandomGen:
    '''Generator of random polynomials'''
    def __init__(self, params):
        '''Constructor
        
        Parameters:
            params (Params): encryption parameters
        '''
        if not isinstance(params, Params):
            raise TypeError("Incorrect parameters");

        self.params = params;

    def get_ternary(self, weight = None):
        '''Generate a polynomial with ternary coefficients

        Parameters:
            weight (in ZZ): the Hamming weight of the result

        Returns:
            u (poly in R<y>): random polynomial with ternary coefficients
        '''
        if weight == None:
            coefs = [ZZ.random_element(-1,2) for i in range(self.params.n)];
            upoly = R(coefs);
            u = RPoly(self.params, upoly);
            return u;

        if not (weight in ZZ):
            raise TypeError("The Hamming weight must be a positive integer");

        if weight < 0:
            raise TypeError("The Hamming weight must be a positive integer");

        coefs = [0 for i in range(self.params.n)];
        count = 0;
        nzset = Set([-1,1]);
        while count < weight:
            coef = ZZ.random_element(self.params.n);
            if coefs[coef] == 0:
                coefs[coef] = nzset.random_element();
                count+=1;
        upoly = R(coefs);
        u = RPoly(self.params, upoly);
        return u;

    def get_ternary_zo(self, prob):
        '''Generate a polynomial with ternary coefficients, where non-zero coefficients occur with certain probability

        Parameters:
            prob (float in [0,1]): probability of sampling a non-zero coefficient

        Returns:
            u (poly in R<y>): polynomial with ternary coefficients
        '''
        if prob < 0 or prob > 1:
            raise TypeError("Probability must be between 0 and 1");

        coefs = [0 for i in range(self.params.n)];
        for i in range(self.params.n):
            tmp = random();
            if tmp <= prob/2:
                coefs[i] = -1;
            elif tmp <= prob:
                coefs[i] = 1;
            else:
                coefs[i] = 0;
        upoly = R(coefs);
        u = RPoly(self.params, upoly);
        return u;

    def get_gaussian(self):
        '''Generate a random element from R_q<y> according to a discrete gaussian distribution

        Returns:
            e (poly in R<y>): random polynomial
        '''

        coefs = []
        for i in range(self.params.n):
            r = d_gauss();
            coefs += [r];
        epoly = R(coefs);
        e = RPoly(self.params, epoly);
        return e;

    def get_uniform(self):
        '''Generate a uniformly random element from R_q<y>

        Returns:
            a (poly in R<y>): polynomial with random coefficients in Z_q
        '''
        mincoef=-ceil((self.params.q-1)/2)
        maxcoef=floor((self.params.q-1)/2)
        coefs = [ZZ.random_element(mincoef, maxcoef + 1) for i in range(self.params.n)]
        apoly = R(coefs);
        a = RPoly(self.params, apoly);
        return a;

#################CIPHERTEXT##########################
class Ctxt:
    '''Ciphertext class'''
    def __init__(self, clist, params, scale = 1):
        '''Constructor
        
        Parameters:
            clist (list of RPoly): polynomial components from R_q
            scale (float): encoding scale
            scheme (str): scheme type ('FV'/'HEAAN'/'HEAAN_FV_KS')
            params (Params): encryption parameters
        '''

        self.c = clist;
        for poly in self.c:
            if not (poly.params == params):
                raise ValueError("The polynomial parameters should allign with encryption parameters");
        if scale <= 0:
            raise ValueError("Encoding scale must be positive");
        self.scale = scale;
        self.params = params;

    def set_scale(self, scale):
        '''Change the encoding scale
            
        Parameters:
            scale (float): new encoding scale
        '''
        if scale <= 0:
            raise ValueError("Encoding scale must be positive");
        self.scale = scale;

#############ENCODER OF COMPLEX-VALUED VECTORS##############
class CyclIntEncoder():
    '''The encoder of complex vectors into cyclotomic integers via the canonical embedding'''

    def __init__(self, scale, slots):
        '''Constructor

        Parameters:
            scale (float, int): scaling parameter to reduce the rounding error
            slots (int): the dimension of complex valued vectors to be encoded and decoded 
        '''
        if scale < 1.0:
            raise ValueError("Scale must be bigger than one");
        if not (log(slots,2) in ZZ):
            raise ValueError("Dimension must be a power of 2");

        self.scale = scale;
        self.dim = 2*slots;

        zt = exp(pi*I/self.dim);
        zt_inv = exp(-pi*I/self.dim);
        self.roots = [0 for _ in range(self.dim)];
        self.inv_roots = [0 for _ in range(self.dim)];
        self.roots[0] = 1.0;
        self.inv_roots[0] = 1.0;
        for i in range(1,self.dim):
            self.roots[i] = (self.roots[i-1] * zt).n();
            self.inv_roots[i] = (self.inv_roots[i-1] * zt_inv).n();
        self.inv_roots = bit_reverse(self.inv_roots);

    def encode_vector(self, vec):
        '''Encode a vector of complex numbers into a cyclotomic integer

        Parameters:
            vec (array in CC): k-dimensional array of complex values

        Returns:
            res (CyclInt): cyclotomic integer
        '''
        vec_len = len(vec);
        if 2*vec_len != self.dim:
            raise ValueError("The input vector dimension is not equal to the encoder packing capacity.");

        #Expand the input vector with conjugate values in the reversed order
        conj_vec = [conjugate(vec[vec_len-1-i]) for i in range(vec_len)];
        res = vec + conj_vec;

        res = bit_reverse(res);

        cur_dim = 2;
        start_zt_pwr = self.dim/2;
        while cur_dim <= self.dim:
            for offset in range(0, self.dim, cur_dim):
                for k in range(0, cur_dim/2):
                    u = res[k + offset];
                    v = res[k + offset + cur_dim/2];
                    res[k + offset] = u + v;
                    res[k + offset + cur_dim/2] = (u - v) * self.inv_roots[start_zt_pwr + offset/cur_dim];
            cur_dim *= 2;
            start_zt_pwr /= 2;

        for i in range(len(res)):
            if res[i] in CC:
                res[i] = CC(res[i]).real();
            res[i] = round(res[i]/self.dim * self.scale);
        res = R(res);
        res = CyclInt(2*self.dim, res);

        return res;

    def decode_vector(self, cycl_int, scale):
        '''Decode a vector of complex numbers into a cyclotomic integer

        Parameters:
            cycl_int (CyclInt): cyclotomic integer encoding a vector of complex numbers

        Returns:
            res (array in CC): k-dimensional array of complex values
        '''
        if cycl_int.dim != self.dim:
            raise ValueError("The dimension of the cyclotomic integer is not equal to the encoder dimension.")
        
        coefs = list(cycl_int.poly);
        coefs = coefs + (self.dim - len(coefs))* [0];
        coefs = bit_reverse(coefs);

        cur_dim = 2;
        while cur_dim <= self.dim:
            start_zeta_pwr = self.dim/cur_dim;
            zeta_pwr_leap = 2*start_zeta_pwr;
            for offset in range(0, self.dim, cur_dim):
                for k in range(0, cur_dim/2): 
                    u = coefs[k + offset];
                    v = coefs[k + offset + cur_dim/2] * self.roots[start_zeta_pwr + k * zeta_pwr_leap];
                    coefs[k + offset] = u + v;
                    coefs[k + offset + cur_dim/2] = u - v;
            cur_dim *= 2;

        res = [(coefs[i]/float(scale)).n() for i in range(self.dim/2)];
        return res;
#################FV/HEAAN SCHEME##########################
class Scheme:
    '''Class containing all operations of homomorphic schemes'''
    def __init__(self, params):
        '''Constructor
        
        Parameters:
            params (Params): encryption parameters
        '''
        if not isinstance(params, Params):
            raise TypeError("Incorrect parameters");
        if not params.plain_init:
            raise ValueError("Plaintext parameters are not set up");
        
        self.params = params;
        self.sampler = RandomGen(params);
        self.sk_init = False;
        self.pk_init = False;
        self.rlk_init = False;
        self.encdr_init = False;
        #in the original HEAAN scheme secret keys are sparse and have a fixed Hamming weight
        if self.params.type == 'HEAAN':
            self.h = 128;

    def sk_gen(self):
        '''Generates a secret key'''
        if self.params.type == 'FV':
            self.sk = self.sampler.get_ternary();
        elif self.params.type == 'HEAAN':
            self.sk = self.sampler.get_ternary(self.h);
        elif self.params.type == 'HEAAN_FV_KS':
            self.sk = self.sampler.get_ternary();
        else:
            raise NotImplementedError("This scheme type is not supported to generate relinearisation keys.");
        self.sk_init = True;

    def pk_gen(self):
        '''Generates a public key'''
        if not self.sk_init:
            raise ValueError("Secret key is not generated");

        a = self.sampler.get_uniform();
        e = self.sampler.get_gaussian();
        b = -a*self.sk - e;
        b.modq();
        self.pk = (b, a);
        self.pk_init = True;

    def rlk_gen(self):
        '''Generates evaluation keys'''
        if not self.sk_init:
            raise ValueError("Secret key is not generated");

        if self.params.type == 'HEAAN':
            #set large modulus
            Q = self.params.q^2;
            Qsampler = copy.deepcopy(self.sampler);
            Qsampler.params.set_mod(Q);
            #the secret key mod Q
            Qsk = copy.deepcopy(self.sk);
            Qsk.params.set_mod(Q);
            Qss = Qsk * Qsk;
            #generate random elements in R_Q
            a = Qsampler.get_uniform();
            e = Qsampler.get_gaussian();
            b = -a * Qsk - e + Qss * self.params.q;
            b.modq();
            self.rlk = (b,a);

            print("Scheme q:", log(self.params.q, 2));
            print("Relin Q:", log(self.rlk[0].params.q, 2));
        elif self.params.type == 'FV' or self.params.type == 'HEAAN_FV_KS':
            self.rlk = [];
            ss = self.sk * self.sk;
            for i in range(self.params.l+1):
                ai = self.sampler.get_uniform();
                ei = self.sampler.get_gaussian();
                bi = -ai*self.sk - ei + ss*self.params.w^i;
                bi.modq();
                self.rlk += [(bi,ai)];
        else:
            raise NotImplementedError("This scheme type is not supported to generate relinearisation keys.");

        self.rlk_init = True;

    def all_key_gen(self):
        '''Generates all keys'''
        self.sk_gen();
        self.pk_gen();
        self.rlk_gen();

    def encrypt_poly(self, pt, scale = 1.0):
        '''Encrypts a plaintext polynomial

        Parameters:
            pt (Rpoly): plaintext polynomial
            scale (float): encoding scale 

        Returns:
            ct (Ctxt): ciphertext 
        '''
        if not self.pk_init:
            raise ValueError("Public key is not generated");

        e0 = self.sampler.get_gaussian();
        e1 = self.sampler.get_gaussian();

        if self.params.type == 'FV':
            u = self.sampler.get_ternary();
            c0 = self.params.Delta * pt + self.pk[0] * u + e0;
        elif self.params.type == 'HEAAN' or self.params.type == 'HEAAN_FV_KS':
            u = self.sampler.get_ternary_zo(0.5);
            c0 = pt + self.pk[0] * u + e0;
        
        c0.modq()
        c1 = self.pk[1] * u + e1;
        c1.modq();

        ct = Ctxt([c0, c1], self.params, scale);
        return ct;

    def decrypt_poly(self, ct):
        '''Decrypts a ciphertext

        Parameters:
            ct (Ctxt): ciphertext

        Returns:
            pt (Rpoly): plaintext polynomial
        '''
        if not self.sk_init:
            raise ValueError("Secret key is not generated");

        pt = ct.c[0];
        tmp_sk = copy.deepcopy(self.sk);
        tmp_sk.params.set_mod(ct.params.q);
        sk_pwr = tmp_sk;
        for i in range(1,len(ct.c)):
            pt = pt + ct.c[i] * sk_pwr;
            sk_pwr = sk_pwr * tmp_sk;
        pt.modq();

        if self.params.type == 'FV':
            pt = pt * self.params.g;
            pt.scale_round(self.params.q);
            pt.modt();
        
        return pt;

    def is_decrypted_to(self, ct, pt):
        '''Checks whether the given ciphertext contains the given plaintext

        Parameters:
            ct (Ctxt): ciphertext
            pt (poly in R<y>): plaintext 

        Returns:
            (bool): True if the given ciphertext encrypts the given plaintext, False otherwise
        '''
        if self.params.type == 'HEAAN' or self.params.type == 'HEAAN_FV_KS':
            raise ValueError("Since plaintext contain noise, this function is useless in HEAAN");

        if self.params.type == 'FV':
            pt_dec = self.decrypt_poly(ct);

            dif = pt_dec.poly - pt.poly;
            if dif == R(0):
                return True;
            
            ls = list(dif);
            for z in ls:
                if z%self.params.p != 0:
                    return False;
            return True;

    def add(self, ct1, ct2):
        '''Adds two ciphertext messages

        Parameters:
            ct1 (Ctxt): ciphertext 1
            ct2 (Ctxt): ciphertext 2

        Returns:
            res (Ctxt in R^2<y>): sum of two ciphertexts
        '''
        if len(ct1.c) != 2:
            raise ValueError("Ciphertext 1 dimension is not 2.");
        if len(ct2.c) != 2:
            raise ValueError("Ciphertext 2 dimension is not 2.");
        if ct1.scale != ct2.scale:
            raise ValueError("Different ciphertext scales.")
        if not (ct1.params == ct2.params):
            if ct1.params.type == 'FV' or ct2.params.type == 'FV':
                raise ValueError("Ciphertexts should have same parameters");
            elif ct1.params.q != ct2.params.q:
                while ct1.params.q < ct2.params.q:
                    ct2 = self.mod_down(ct2);
                while ct1.params.q > ct2.params.q:
                    ct1 = self.mod_down(ct1);

        res0 = ct1.c[0] + ct2.c[0];
        res0.modq();
        res1 = ct1.c[1] + ct2.c[1];
        res1.modq();

        res = Ctxt([res0, res1], ct1.params, ct1.scale);

        return res;

    def basic_mul(self, ct1, ct2):
        '''Basic multiplication of two ciphertext (convolution of ciphertext tuples)

        Parameters:
            ct1 (Ctxt): ciphertext 1
            ct2 (Ctxt): ciphertext 2

        Returns:
            res (Ctxt): product of two ciphertext of dimension 3
        '''
        if len(ct1.c) != 2:
            raise ValueError("Ciphertext 1 dimension should be 2");
        if len(ct2.c) != 2:
            raise ValueError("Ciphertext 2 dimension should be 2");
        if not (ct1.params == ct2.params):
            if ct1.params.type == 'FV' or ct2.params.type == 'FV':
                raise ValueError("Ciphertexts should have same parameters");
            elif ct1.params.q != ct2.params.q:
                while ct1.params.q < ct2.params.q:
                    ct2 = self.mod_down(ct2);
                while ct1.params.q > ct2.params.q:
                    ct1 = self.mod_down(ct1);
        
        if ct1.params.type == 'FV':
            #Karatsuba multiplication of g * (ct1[0] + ct1[1] * X) and g * (ct2[0] + ct2[1] * X)
            c0 = ct1.params.g * ct1.c[0] * ct2.c[0];
            c2 = ct1.params.g * ct1.c[1] * ct2.c[1];
            c1 = ct1.params.g * (ct1.c[0] + ct1.c[1]) * (ct2.c[0] + ct2.c[1]) - c0 - c2;

            c0.scale_round(ct1.params.q);
            c1.scale_round(ct1.params.q);
            c2.scale_round(ct1.params.q);
        elif ct1.params.type == 'HEAAN' or ct1.params.type == 'HEAAN_FV_KS':
            #Karatsuba multiplication of (ct1[0] + ct1[1] * X) and (ct2[0] + ct2[1] * X)
            c0 = ct1.c[0] * ct2.c[0];
            c2 = ct1.c[1] * ct2.c[1];
            c1 = (ct1.c[0] + ct1.c[1]) * (ct2.c[0] + ct2.c[1]) - c0 - c2;

        c0.modq();
        c1.modq();
        c2.modq();
        
        res = Ctxt([c0,c1,c2], ct1.params, ct1.scale*ct2.scale);

        return res;

    def relin(self, ct):
        '''Relinearizes a 3-dimensional ciphertext

        Parameters:
            ct (Ctxt): ciphertext of dimension 3

        Returns:
            res (Ctxt): resulting ciphertext
        '''
        if not self.rlk_init:
            raise ValueError("Relinarization keys are not generated");

        c0 = ct.c[0];
        c1 = ct.c[1];

        if self.params.type == 'FV' or self.params.type == 'HEAAN_FV_KS':
            l2 = len(list(ct.c[2].poly));
            c2_signs = [sign(ct.c[2].poly[j]) for j in range(l2)];
            c2 = [abs(ct.c[2].poly[j]) for j in range(l2)];
            for i in range(ct.params.l + 1):
                c2i_coef = [];
                for j in range(l2):
                    if ZZ(c2[j]%ct.params.w) > ct.params.w/2:
                        c2i_coef += [c2_signs[j] * (ZZ(c2[j]%ct.params.w) - ct.params.w)];
                        c2[j] = ZZ((c2[j] - ZZ(c2[j]%ct.params.w)) / ct.params.w) + 1;
                    else:
                        c2i_coef += [c2_signs[j] * ZZ(c2[j]%ct.params.w)];
                        c2[j] = ZZ((c2[j] - ZZ(c2[j]%ct.params.w)) / ct.params.w);
                c2i = RPoly(ct.params, R(c2i_coef));

                rlk0 = copy.deepcopy(self.rlk[i][0]);
                rlk0.params.set_mod(ct.params.q);
                rlk1 = copy.deepcopy(self.rlk[i][1]);
                rlk1.params.set_mod(ct.params.q);

                c0 = c0 + rlk0 * c2i;
                c1 = c1 + rlk1 * c2i;

                c0.modq();
                c1.modq();
        elif self.params.type == 'HEAAN':
            c2 = copy.deepcopy(ct.c[2]);

            #relinearisation modulus
            Q = self.rlk[0].params.q;

            #lift c2 to the relinearisation modulus
            c2.params.set_mod(Q);

            #multiply c2 by the relinearisation key
            d0 = self.rlk[0] * c2;
            d1 = self.rlk[1] * c2;

            #scale and round by the initial q
            d0.scale_round(self.params.q);
            d1.scale_round(self.params.q);

            #change the modulus of d0 and d1 back to the ciphertext modulus
            d0.params.set_mod(ct.params.q);
            d1.params.set_mod(ct.params.q);

            c0 = c0 + d0;
            c1 = c1 + d1;

            c0.modq();
            c1.modq();
        else:
            raise NotImplementedError("Relinearisation is not supported in this scheme.");

        res = Ctxt([c0,c1], ct.params, ct.scale);

        return res;

    def mul(self, ct1, ct2):
        '''Multiplies two ciphertext messages

        Parameters:
            ct1 (Ctxt): ciphertext 1
            ct2 (Ctxt): ciphertext 2
        
        Returns:
            (Ctxt): product of two ciphertext of dimension 2
        '''
        res = self.relin(self.basic_mul(ct1, ct2));
        if res.params.type == 'HEAAN' or res.params.type == 'HEAAN_FV_KS':
            res = self.rescale(res);

        print("Log scale after mul: ", log(res.scale,2));

        return res;

    def rescale(self, ct):
        '''Rescale a ciphertext by the encoding scale

        Parameters:
            ct (Ctxt): ciphertext

        Returns:
            res (Ctxt): rescaled ciphertext
        '''
        if len(ct.c) != 2:
            raise ValueError("Ciphertext dimension should be 2");
        if not self.encdr_init:
            raise ValueError("Encoder must be initialized");
        if ct.params.type != 'HEAAN' and ct.params.type != 'HEAAN_FV_KS':
            raise NotImplementedError("Implemented only for HEAAN");

        new_q = ct.params.q / self.encdr.scale;

        if not (new_q in ZZ):
            raise ValueError("New ciphertext modulus must be an integer");

        c0 = copy.deepcopy(ct.c[0]);
        c0.scale_round(self.encdr.scale);
        c0.params.set_mod(new_q);
        c1 = copy.deepcopy(ct.c[1]);
        c1.scale_round(self.encdr.scale);
        c1.params.set_mod(new_q);

        print("Old modulus: ", log(ct.params.q, 2));
        new_params = copy.deepcopy(c1.params);
        print("New modulus: ", log(new_params.q, 2));

        res = Ctxt([c0,c1], new_params, ct.scale/self.encdr.scale);

        return res;

    def encode_cycl_int(self, cycl_int, params):
        '''Encode a cyclotomic integer into the ring of integers R

        Parameters:
            cycl_int (CyclInt): cyclotomic integer

        Returns:
            res (RPoly): polynomial encoding of a cyclotomic integer
        '''
        if cycl_int.dim != params.m:
            raise ValueError("The dimensions of the ring of integers and the cyclotomic ring of the input must be equal.");

        coefs = list(cycl_int.poly);
        enc = R(0);

        if params.type == 'FV':
            scal = 1;
            enc_coefs = [0 for _ in range(params.n)];
            for i in range(len(coefs)):
                c = ZZ(coefs[i]*scal % params.p);
                if c > params.p/2:
                    c -= params.p;
                expan = balanced_expansion(c, params.n/params.m, params.b);
                for j in range(len(expan)):
                    enc_coefs[params.m*j+i] = (-1)^j * expan[j];
                scal = (scal*params.beta) % params.p;
            enc = R(enc_coefs);
        elif params.type == 'HEAAN' or params.type == 'HEAAN_FV_KS':
            d = ZZ(params.n/params.m);
            enc_coefs = [0 for _ in range(params.n)];
            for i in range(len(coefs)):
                c = ZZ(coefs[i] % params.q);
                if c > params.q//2:
                    c -= params.q;
                enc_coefs[i*d] = c;
            enc = R(enc_coefs);

        res = RPoly(params, enc);
        return res;

    def decode_cycl_int(self, rpoly):
        '''Decodes a plaintext to a cyclotomic integer

        Parameters:
            rpoly (RPoly): plaintext to decode

        Returns:
            res (CyclInt): cyclotomic integer

        '''
        poly = R(0);
        if self.params.type == 'FV':
            rpoly.mod_poly(self.params.g);
            coefs = [0 for _ in range(self.params.m)];
            coefs[0] = rpoly.poly[0];
            alphai = mod(1, self.params.p);
            for i in range(1, self.params.m):
                alphai *= mod(self.params.alpha, self.params.p);
                if rpoly.poly[i] == 0:
                    continue;
                coef = ZZ(mod(rpoly.poly[i], self.params.p) * alphai);
                if coef > self.params.p/2:
                    coef -= self.params.p;
                coefs[i] = coef;
            poly = R(coefs);
        elif self.params.type == 'HEAAN' or self.params.type == 'HEAAN_FV_KS':
            d = ZZ(self.params.n/self.params.m);
            coefs = [0 for _ in range(self.params.n)];
            for i in range(0, self.params.n, d):
                coefs[i/d] = rpoly.poly[i];
            poly = R(coefs);

        res = CyclInt(2*self.params.m, poly);
        return res;

    def is_encodable(self, cycl_int):
        '''Checks whether the given cyclotomic integer can be correctly encoded into the plaintext space, i.e. the coefficients of cycl_int are not bigger in absolute value than p/2

        Parameters:
            cycl_int (CyclInt): cyclotomic integer
            
        Returns:
            (bool): True if the given cyclotomic integer is encodable, False otherwise
        '''
        coefs = list(cycl_int.poly);
        if len(coefs) == 0:
            return True;
        max_coef = max([abs(coef) for coef in coefs]);
        print("Max plaintext coef (log): ", log(max_coef, 2).n());

        bound = 0;
        if self.params.type == 'FV':
            bound = self.params.p;
        elif self.params.type == 'HEAAN' or self.params.type == 'HEAAN_FV_KS':
            bound = self.params.q;

        if 2*max_coef >= bound:
            return False;
        return True;

    def set_encoder(self, encdr):
        '''Set an encoder of complex vectors

        Parameters:
            encdr (CyclIntEncoder): encoder
        '''
        if not (self.params.m/encdr.dim in ZZ):
            raise ValueError("Encoder dimension should divide the degree of the plaintext polynomial");
        if not (self.params.q/encdr.scale in ZZ):
            raise ValueError("Encoder scale should divide the ciphertext modulus");

        self.encdr = encdr;
        self.encdr_init = True;

    def encrypt_vector(self, vec):
        '''Encrypt a vector of complex numbers

        Parameters:
            vec (array in CC): complex-valued vector to encode

        Returns:
            ct (Ctxt): ciphertext
        '''
        if not self.encdr_init:
            raise ValueError("Encoder is not instantiated.");
        if 2 * len(vec) != self.encdr.dim:
            raise ValueError("The input vector has a wrong size.");

        cycl_int = self.encdr.encode_vector(vec);
        pt = self.encode_cycl_int(cycl_int, self.params);
        ct = self.encrypt_poly(pt, self.encdr.scale);

        return ct;

    def decrypt_vector(self, ct):
        '''Decrypt a ciphertext to a complex-valued vector

        Parameters:
            ct (Ctxt): ciphertext to decrypt

        Returns:
            res (array in CC): decrypted complex-valued vector
            
        '''
        if not self.encdr_init:
            raise ValueError("Encoder is not instantiated.");

        scale = ct.scale;
        pt = self.decrypt_poly(ct);
        cycl_int = self.decode_cycl_int(pt);
        res = self.encdr.decode_vector(cycl_int, scale);

        return res;

    def mul_by_real(self, ct, real_num):
        '''Multiplies a ciphertext by a real number

        Parameters:
            ct (Ctxt): ciphertext
            real_num (float): real scalar

        Returns:
            res (Ctxt): resulting ciphertext
        '''
        if not self.encdr_init:
            raise ValueError("The encoder of complex vectors is not instantiated.")

        vec = [real_num for _ in range(self.params.m/2)];
        real_num_cycl_int = self.encdr.encode_vector(vec);
        real_num_plain = self.encode_cycl_int(real_num_cycl_int, ct.params);

        c0 = real_num_plain * ct.c[0];
        c0.modq();
        c1 = real_num_plain * ct.c[1];
        c1.modq();

        res = Ctxt([c0,c1], ct.params, self.encdr.scale*ct.scale);

        if self.params.type == 'HEAAN' or self.params.type == 'HEAAN_FV_KS':
            res = self.rescale(res);

        return res;

    def mod_down(self, ct):
        '''Scales down the ciphertext modulus of a given ciphertext by the encoding scale

        Parameters:
            ct (Ctxt): ciphertext

        Returns:
            res(Ctxt): ciphertext with a reduced ciphertext modulus
        '''
        if not self.encdr_init:
            raise ValueError("The encoder of complex vectors is not instantiated.")

        new_q = ct.params.q / self.encdr.scale;

        if not (new_q in ZZ):
            raise ValueError("New ciphertext modulus must be an integer");

        print("Old modulus: ", log(ct.params.q, 2));

        c0 = copy.deepcopy(ct.c[0]);
        c0.params.set_mod(new_q);
        c0.modq();

        c1 = copy.deepcopy(ct.c[1]);
        c1.params.set_mod(new_q);
        c1.modq();

        res = Ctxt([c0,c1], c1.params, ct.scale);

        print("New modulus: ", log(res.params.q, 2));

        return res;

    def fresh_noise(self, q, coef_bound = 0):
        '''Outputs a heuristic estimate of fresh ciphertext noise
        
        Parameters:
            q (int): ciphertext modulus
            coef_bound (float): bound on the infinity norm of a plaintext (only for HEAAN and HEAAN_FV_KS)

        Returns:
            res (float): noise estimation
        '''

        res = 0;

        if self.params.type == 'FV':
            N_b = self.params.n;
            if self.params.b == 2:
                N_b /= 2;
            res = (self.params.b + 1) / q * (sqrt(3 * self.params.n) / 2 * (self.params.b + 1) * N_b + 2 * st_dev * self.params.n * sqrt(12 + 9 / self.params.n));
        elif self.params.type == 'HEAAN_FV_KS':
            res = 8 * sqrt(2) * st_dev * self.params.n + 6 * st_dev * sqrt(self.params.n) + 16 * st_dev*self.params.n;
            res += coef_bound;
        elif self.params.type == 'HEAAN':
            res = 8 * sqrt(2) * st_dev * self.params.n + 6 * st_dev * sqrt(self.params.n) + 16 * st_dev*sqrt(self.h * self.params.n);
            res += coef_bound;

        return res;

    def rescale_noise(self, noise):
        '''Outputs a heuristic estimate of ciphertext noise after rescaling

        Parameters:
            noise (float): input noise
        Returns:
            res (float): noise after rescaling
        '''
        res = 0;
        if self.params.type == 'HEAAN' or self.params.type == 'HEAAN_FV_KS':
            res = noise/self.encdr.scale + sqrt(self.params.n/3) * (3 + 8 * sqrt(self.params.n));
        else:
            raise ValueError("Rescaling for this scheme is not supported.")

        return res;

    def add_noise(self, noise1, noise2):
        '''Outputs a heuristic estimate of ciphertext noise after addition
        
        Parameters:
            noise1 (float): noise of the first ciphertext
            noise2 (float): noise of the second ciphertext

        Returns:
            res (float): noise after addition
        '''

        res = 0;

        if self.params.type == 'HEAAN' or self.params.type == 'HEAAN_FV_KS' or self.params.type == 'FV':
            res = noise1 + noise2;
        else:
            raise ValueError("Noise estimation after addition for this scheme is not supported.");

        return res;

    def mul_noise(self, noise1, noise2, q, q_level = 0):
        '''Outputs a heuristic estimate of ciphertext noise after multiplication
        
        Parameters:
            noise1 (float): noise of the first ciphertext
            noise2 (float): noise of the second ciphertext
            q (int): ciphertext modulus
            q_level (int): current ciphertext modulus (only for HEAAN)

        Returns:
            res (float): noise after multiplication
        '''

        res = 0;

        if self.params.type == 'HEAAN':
            bound_ks = 8 * st_dev * self.params.n / sqrt(3);
            bound_mul = q^(-1) * q_level * bound_ks;
            res = noise1 * noise2 + bound_mul;
            res = self.rescale_noise(res);
        elif self.params.type == 'HEAAN_FV_KS':
            bound_ks = st_dev * self.params.n * self.params.w * sqrt(3*(self.params.l + 1));
            bound_mul = bound_ks;
            res = noise1 * noise2 + bound_mul;
            res = self.rescale_noise(res);
        elif self.params.type == 'FV':
            res = (self.params.b + 1) * sqrt(3 * self.params.n + 2 * self.params.n^2) * (noise1 + noise2) + 3 * noise1 * noise2 + (self.params.b + 1) / q * (sqrt(3 * self.params.n + 2 * self.params.n^2 + 4 * self.params.n^3 / 3) + st_dev * self.params.n * self.params.w * sqrt(3*(self.params.l + 1))); 
        else:
            raise ValueError("Noise estimation after multiplication for this scheme is not supported.");

        return res;

    def mul_by_real_noise(self, noise, const):
        '''Outputs a heuristic estimate of multiplication by a constant
        
        Parameters:
            noise (float): noise of the first ciphertext
            const (float): constant to multiply with

        Returns:
            res (float): noise estimation after multiplication
        '''
        res = 0;

        if self.params.type == 'HEAAN' or self.params.type == 'HEAAN_FV_KS':
            const_coef = round(self.encdr.scale * const);
            if const_coef == 0:
                raise ValueError("Encoding scale is too small");
            res = noise * abs(const_coef);
            res = self.rescale_noise(res);
        elif self.params.type == 'FV':
            const_coef = round(self.encdr.scale * const);
            if const_coef == 0:
                raise ValueError("Encoding scale is too small");
            max_wt = log(abs(const_coef), self.params.b);
            res = ((self.params.b+1)/2 + self.params.b/2 * (max_wt - 1)) * noise;
        else:
            raise ValueError("Noise estimation after multiplication by a constant for this scheme is not supported.");

        return res;

    def is_q_valid_for_poly_eval(self, q, coefs, data_bound = 0):
        '''Outputs whether a polynomial function can be evaluated correctly

        Parameters:
            q (int): ciphertext modulus to test
            coefs (array of floats): coefficients of a polynomial function
            data_bound (float): bound on the infinity norm of the input vector 

        Returns:
            (bool): True if a polynomial function can be correctly evaluated with given parameters, False otherwise
        '''
        if not (self.params.type in sprtd_schemes):
            raise ValueError("Noise estimation after polynomial evaluation for this scheme is not supported.");

        deg = len(coefs)-1;
        depth = ceil(log(deg,2));

        x_pwr_noise = [0 for _ in range(depth+1)];
        
        # encrypt and encode powers of the input x
        if self.params.type == "FV":
            x_pwr_noise[0] = self.fresh_noise(q);
        elif self.params.type == "HEAAN" or self.params.type == "HEAAN_FV_KS":
            coef_bound = round(self.encdr.scale * data_bound);
            x_pwr_noise[0] = self.fresh_noise(q, coef_bound);

        res_noise = 0;

        i = 1;
        while (2^i <= deg):
            x_pwr_noise[i] = self.mul_noise(x_pwr_noise[i-1], x_pwr_noise[i-1], q, q/self.encdr.scale^(i-1));
            i += 1;

        for i in range(deg + 1):
            const = coefs[i];
            if const == 0:
                continue;

            is_first_pwr = True;

            tmp_noise = 0;
            tmp_q = q;

            bin_exp = bin(i)[-1:1:-1];
            for j in range(len(bin_exp)):
                if bin_exp[j] == '1':
                    if is_first_pwr:
                        if const != 1 or i != deg:
                            tmp_noise = self.mul_by_real_noise(x_pwr_noise[j], const);
                            tmp_q = q/self.encdr.scale^(j+1);
                        else:
                            tmp_noise = x_pwr_noise[j];
                            tmp_q = q/self.encdr.scale^j;
                        is_first_pwr = False;
                    else:
                        new_tmp_q = min(tmp_q, q / self.encdr.scale^j);
                        tmp_noise = self.mul_noise(tmp_noise, x_pwr_noise[j],q, new_tmp_q);
                        tmp_q = new_tmp_q;

            # Align the encoding scale
            if self.params.type == 'FV':
                tmp_noise = self.mul_by_real_noise(tmp_noise, self.encdr.scale^(deg - i - 1));

            if res_noise == 0:
                res_noise = tmp_noise;
            else: 
                res_noise = self.add_noise(res_noise, tmp_noise);

        if coefs[deg] == 1:
            res_q = q / self.encdr.scale^(ceil(log(deg,2)));
        else:
            res_q = q / self.encdr.scale^(ceil(log(deg+1,2)));

        if self.params.type == 'HEAAN' or self.params.type == "HEAAN_FV_KS":
            if res_q < 2:
                return False;
            res_noise /= res_q;

        return (res_noise.n() < 1/2)

    def get_enc_scale(self, prec):
        '''Computes an encoding scale supporting a given input precision

        Parameters:
            prec (int): input precision

        Returns:
            res (int): encoding scale for HEAAN 
        '''
        res = 0

        if self.params.type == 'HEAAN':
            init_noise_bound = 8 * sqrt(2) * st_dev * self.params.n + 6 * st_dev * sqrt(self.params.n) + 16 * st_dev * sqrt(self.h * self.params.n); 
            res = self.params.m / 2 * prec * (1 + 2 * init_noise_bound);
            res = 2^ceil(log(res,2));
            print("log of the HEAAN encoding scale needed: ", log(res, 2).n());
        elif self.params.type == 'HEAAN_FV_KS':
            init_noise_bound = 8 * sqrt(2) * st_dev * self.params.n + 6 * st_dev * sqrt(self.params.n) + 16 * st_dev*self.params.n;
            res = self.params.m / 2 * prec * (1 + 2 * init_noise_bound);
            res = 2^ceil(log(res,2));
            print("log of the HEAAN_FV_KS encoding scale needed: ", log(res, 2).n());
        elif self.params.type == 'FV':
            res = self.params.m / 2 * prec;
            print("log of the FV encoding scale needed: ", log(res, 2).n());

        return res;

    def min_q_for_poly_eval(self, coefs, inp_bound):
        '''Outputs the minimal ciphertext modulus supporting evaluation of a polynomial function with given coefficients and an input bound

        Parameters:
            coefs (array of floats): coefficients of a polynomial function
            inp_bound (int): bound on absolute values of data

        Returns:
            q (int): ciphertext modulus
        '''
        left = 1;
        right = int(log(self.params.q, 2));

        if not self.is_q_valid_for_poly_eval(2^right, coefs, inp_bound):
            print("These encryption parameters do not support 128-bits of security.");
            return 0;

        log_q = right;

        while left <= right:
            middle = floor((left + right) / 2);
            if self.is_q_valid_for_poly_eval(2^middle, coefs, inp_bound):
                right = middle - 1;
                log_q = middle;
            else:
                left = middle + 1;

        print("log q: ", log_q);

        return 2^log_q;

    def is_correct_form(self, ct, pt, cycl_int):
        '''Tests if the given ciphertext, plaintext and cyclotomic integer can be correctly decrypted/decoded by the given scheme

        Parameters:
            ct (Ctxt): ciphertext
            pt (Rpoly): plaintext
            cycl_int (CyclInt): cyclotomic integer

        Returns:
            (bool): True if decryption and decoding work correctly, False otherwise
        '''

        decrpt_ok = True;
        decd_ok = True;

        if self.params.type == 'FV':
            if not self.is_decrypted_to(ct, pt):
                decrpt_ok = False;
                print("Decryption error");
            if not self.is_encodable(cycl_int):
                decd_ok = False;
                print("Decoding error");
        elif self.params.type == 'HEAAN' or self.params.type == "HEAAN_FV_KS":
            if not self.is_encodable(pt):
                decd_ok = False;
                print("Decoding error");

        return (decrpt_ok and decd_ok);

    def poly_eval_test(self, inp_vec, inp_bound, coefs):
        '''Computes a polynomial function and tests its correctness

        Parameters:
            inp_vec (array of floats): input vector
            inp_bound (float): bound on input values
            coefs (array of floats): coefficients of a polynomial function

        Returns:
            res_ct (Ctxt): resulting ciphertext
            res_vec (array in CC): resulting vector
            res_vec_dec (array in CC): decrypted vector
        '''
        slots = len(inp_vec);
        if slots != self.params.m/2:
            raise ValueError("Input vector should have the same dimension as the encoder");

        inp_cycl = self.encdr.encode_vector(inp_vec);
        inp_pt = self.encode_cycl_int(inp_cycl, self.params);
        inp_ct = self.encrypt_poly(inp_pt, self.encdr.scale);

        dec_vec = self.decrypt_vector(inp_ct);
        approx_err = (vector(inp_vec)-vector(dec_vec)).norm(Infinity);

        print("Initial approx. error: ", log(approx_err.n(),2));

        deg = len(coefs)-1;
        depth = ceil(log(deg,2));

        x_pwr_ct = [0 for _ in range(depth+1)];
        x_pwr_cycl = [0 for _ in range(depth+1)];
        x_pwr_pt = [0 for _ in range(depth+1)];
        x_pwr_vec = [0 for _ in range(depth+1)];
        
        # encrypt and encode powers of the input x
        x_pwr_ct[0] = inp_ct;
        x_pwr_cycl[0] = inp_cycl;
        x_pwr_pt[0] = inp_pt;
        x_pwr_vec[0] = inp_vec;

        res_ct = 0;
        res_pt = 0;
        res_cycl = 0;
        res_vec = 0;

        i = 1;
        while (2^i <= deg):
            print("Computing x^{0}".format(str(2^i)));

            x_pwr_ct[i] = self.mul(x_pwr_ct[i-1], x_pwr_ct[i-1]);

            x_pwr_cycl[i] = x_pwr_cycl[i-1] * x_pwr_cycl[i-1];
            if self.params.type == 'HEAAN' or self.params.type == "HEAAN_FV_KS":
                x_pwr_cycl[i].scale_round(self.encdr.scale);
            x_pwr_pt[i] = x_pwr_pt[i-1] * x_pwr_pt[i-1];
            if self.params.type == 'FV':
                x_pwr_pt[i].modt();
            elif self.params.type == 'HEAAN' or self.params.type == "HEAAN_FV_KS":
                x_pwr_pt[i].scale_round(self.encdr.scale);
            x_pwr_vec[i] = [x_pwr_vec[i-1][j]^2 for j in range(slots)];
            i+=1;

        for i in range(deg + 1):
            const = coefs[i];
            if const == 0:
                continue;
            const_cycl = self.encdr.encode_vector([const for _ in range(slots)]);
            const_pt = self.encode_cycl_int(const_cycl, self.params);

            print("Computing {0} * x^{1}".format(str(const), str(i)));

            tmp_c0 = const_pt;
            if self.params.type == 'FV':
                tmp_c0 = self.params.Delta * tmp_c0;

            tmp_ct = Ctxt([tmp_c0, RPoly(self.params, R(0))], self.params); #ciphertext encrypting const without noise
            if self.params.type == 'HEAAN' or self.params.type == "HEAAN_FV_KS":
                tmp_ct.scale = self.encdr.scale;
                
            tmp_pt = const_pt;
            tmp_cycl = const_cycl;
            tmp_vec = [const for k in range(slots)];

            is_first_pwr = True;

            bin_exp = bin(i)[-1:1:-1];
            for j in range(len(bin_exp)):
                if bin_exp[j] == '1':
                    if is_first_pwr:
                        if const != 1 or i != deg:
                            tmp_ct = self.mul_by_real(x_pwr_ct[j], const);
                            tmp_pt = x_pwr_pt[j] * const_pt;
                            if self.params.type == 'FV':
                                tmp_pt.modt();
                            elif self.params.type == 'HEAAN' or self.params.type == "HEAAN_FV_KS":
                                tmp_pt.scale_round(self.encdr.scale);
                            tmp_cycl = x_pwr_cycl[j] * const_cycl;
                            if self.params.type == 'HEAAN' or self.params.type == "HEAAN_FV_KS":
                                tmp_cycl.scale_round(self.encdr.scale);
                            tmp_vec = [x_pwr_vec[j][k] * const for k in range(slots)];
                        else:
                            tmp_ct = x_pwr_ct[j];
                            tmp_pt = x_pwr_pt[j];
                            tmp_cycl = x_pwr_cycl[j];
                            tmp_vec = x_pwr_vec[j];
                        is_first_pwr = False;
                    else:
                        tmp_ct = self.mul(tmp_ct, x_pwr_ct[j]);
                        tmp_pt = tmp_pt * x_pwr_pt[j];
                        if self.params.type == 'FV':
                            tmp_pt.modt();
                        elif self.params.type == 'HEAAN' or self.params.type == "HEAAN_FV_KS":
                            tmp_pt.scale_round(self.encdr.scale);
                        tmp_cycl = tmp_cycl * x_pwr_cycl[j];
                        if self.params.type == 'HEAAN' or self.params.type == "HEAAN_FV_KS":
                            tmp_cycl.scale_round(self.encdr.scale);
                        tmp_vec = [tmp_vec[k] * x_pwr_vec[j][k] for k in range(slots)];

            if coefs[deg] == 1:
                final_scale_pwr = deg;
            else:
                final_scale_pwr = deg + 1;

            print("Final scale power: ", final_scale_pwr);

            # Align the encoding scale
            if self.params.type == 'FV' and final_scale_pwr >= (i+2):
                tmp_ct = self.mul_by_real(tmp_ct, self.encdr.scale^(final_scale_pwr - i - 2));
                tmp_ct.set_scale(self.encdr.scale^final_scale_pwr);

                tmp_one_cycl = self.encdr.encode_vector([self.encdr.scale^(final_scale_pwr - i - 2) for _ in range(slots)]);
                tmp_cycl = tmp_cycl * tmp_one_cycl;

                tmp_one_pt = self.encode_cycl_int(tmp_one_cycl, self.params);
                tmp_pt = tmp_pt * tmp_one_pt;
                tmp_pt.modt();

            print("Computing the {0}th partial sum...".format(str(i)));

            if res_ct == 0:
                res_ct = tmp_ct;
                res_pt = tmp_pt;
                res_cycl = tmp_cycl;
                res_vec = tmp_vec;
            else:
                res_ct = self.add(res_ct, tmp_ct);
                res_pt = res_pt + tmp_pt;
                res_cycl = res_cycl + tmp_cycl;
                res_vec = [res_vec[j] + tmp_vec[j] for j in range(slots)];

        if not self.is_correct_form(res_ct, res_pt, res_cycl):
            return 0;

        res_vec_dec = self.decrypt_vector(res_ct);

        if res_pt.poly == R(0):
            print("Zero plaintext");
        else:
            print("Plaintext inf. norm:", log(res_pt.poly.norm(Infinity),2).n());

        print("Ciphertext size is {0} Kb".format(str(log(self.params.q, 2) * self.params.n * 2 / 8.0 / 1024.0)));

        return (res_ct, res_vec, res_vec_dec);

#################TESTS###################################
def sine_test(slots, bound, enc_delta, scheme_type, params_index, rounds, b=None):
    '''Computes a sine function approximation and tests its correctness

    Parameters:
        slots (int): number of slots
        bound (int): bound on absolute values of data
        enc_delta (int): encoding scale
        scheme_type (str): scheme type
        params_index (int): parameter index 
        rounds (int): number of test repetitions
        b (int): constant term of the FV plaintext modulus (needed when scheme_type = 'FV')
    '''

    print("Computing the sine function...");

    tailor_deg = 9;
    coefs = [0 for _ in range(tailor_deg + 1)];
    for i in range(1, tailor_deg + 1, 2):
        coefs[i] = (-1)^((i-1)/2)/factorial(i);

    par = Params(scheme_type, params_index);
    par.set_ptxt_params(2*slots, b);
    scheme = Scheme(par);
    encdr = CyclIntEncoder(enc_delta, slots);
    scheme.set_encoder(encdr);

    q = scheme.min_q_for_poly_eval(coefs, bound);
    print("Minimal ciphertext modulus is ", q);
    if q == 0:
        raise ValueError("This parameter set does not support evaluation");
    par.set_mod(q);

    scheme.all_key_gen();

    max_approx_err = -1000.0;
    min_approx_err = 1000.0;

    for rnd in range(rounds):
        inp_vec = [float(bound*(-1)^(ZZ.random_element(2))) for _ in range(slots)];

        res = scheme.poly_eval_test(inp_vec, bound, coefs);
        if res == 0:
            print("Computation failed");

        res_ct = res[0];
        res_vec = res[1];
        res_vec_dec = res[2]; 

        approx_err = (vector([real(res_vec_dec[i]) for i in range(len(res_vec_dec))])-vector(res_vec)).norm(Infinity);
        print("Error between real approximation and encrypted values (log)", log(approx_err,2).n());

        approx_err = (vector([real(res_vec_dec[i]) for i in range(len(res_vec_dec))])-vector([sin(inp_vec[i]) for i in range(len(inp_vec))])).norm(Infinity);
        max_approx_err = max(max_approx_err, log(approx_err,2).n());
        min_approx_err = min(min_approx_err, log(approx_err,2).n());
        if max_approx_err > -7:
            print("Small output precision. Increase parameters.");
            break;

        print("Error between the sine and encrypted values (log)", log(approx_err,2).n());

        approx_err = (vector([real(res_vec[i]) for i in range(len(res_vec))])-vector([sin(inp_vec[i]) for i in range(len(inp_vec))])).norm(Infinity);

        print("Error between the sine and its approximation (log)", log(approx_err,2).n());
        print("Round ", rnd, "has finished");
        print("Max. error so far:", max_approx_err);

    print("After ", rounds, " experiments the maximal approximation error is ", max_approx_err);
    print("and the minimal approximation is ", min_approx_err);
 

def logist(x):
    '''Computes the logistic function

    Parameters:
        x (float): input

    Returns:
        res (float): the logistic function output
    '''

    res = 1/(1+e^(-x));
    return res.n();

def logist_test(slots, bound, enc_delta, scheme_type, params_index, rounds, b=None):
    '''Computes a logistic function approximation and tests its correctness

    Parameters:
        slots (int): number of slots
        bound (int): bound on absolute values of data
        enc_delta (int): encoding scale
        scheme_type (str): scheme type
        params_index (int): parameter index
        rounds (int): number of test repetitions
        b (int): constant term of the FV plaintext modulus (needed when scheme_type = 'FV')
    '''

    print("Computing the logistic function...");

    coefs = [1/2, 1/4, 0, -1/48, 0, 1/480, 0, -17/80640, 0, 31/1451520];

    par = Params(scheme_type, params_index);
    par.set_ptxt_params(2*slots, b);
    scheme = Scheme(par);
    encdr = CyclIntEncoder(enc_delta, slots);
    scheme.set_encoder(encdr);

    q = scheme.min_q_for_poly_eval(coefs, bound);
    print("Minimal ciphertext modulus is ", q);
    if q == 0:
        raise ValueError("This parameter set does not support evaluation");
    par.set_mod(q);

    scheme.all_key_gen();

    max_approx_err = -1000.0;
    min_approx_err = 1000.0;

    for rnd in range(rounds):
        inp_vec = [float(bound*(-1)^(ZZ.random_element(2))) for _ in range(slots)];

        res = scheme.poly_eval_test(inp_vec, bound, coefs);
        if res == 0:
            print("Computation failed");

        res_ct = res[0];
        res_vec = res[1];
        res_vec_dec = res[2]; 

        approx_err = (vector([real(res_vec_dec[i]) for i in range(len(res_vec_dec))])-vector(res_vec)).norm(Infinity);
        print("Error between real approximation and encrypted values (log)", log(approx_err,2).n());

        approx_err = (vector([real(res_vec_dec[i]) for i in range(len(res_vec_dec))])-vector([logist(inp_vec[i]) for i in range(len(inp_vec))])).norm(Infinity);
        max_approx_err = max(max_approx_err, log(approx_err,2).n());
        min_approx_err = min(min_approx_err, log(approx_err,2).n());
        if max_approx_err > -7:
            print("Small output precision. Increase parameters.");
            print("Input: ", inp_vec);
            break;

        print("Error between the logistic regression and encrypted values (log)", log(approx_err,2).n());

        approx_err = (vector([real(res_vec[i]) for i in range(len(res_vec))])-vector([logist(inp_vec[i]) for i in range(len(inp_vec))])).norm(Infinity);

        print("Error between the logistic regression and its approximation (log)", log(approx_err,2).n());
        print("Round ", rnd, "has finished");
        print("Max. error so far:", max_approx_err);

    print("After ", rounds, " experiments the maximal approximation error is ", max_approx_err);
    print("and the minimal approximation is ", min_approx_err);


def power_test(power, slots, bound, enc_delta, scheme_type, params_index, rounds, b=None):
    '''Computes a power function and tests its correctness

    Parameters:
        power (int): exponentiation power
        slots (int): number of slots
        bound (int): bound on absolute values of data
        enc_delta (int): encoding scale
        scheme_type (str): scheme type
        params_index (int): parameter index
        rounds (int): number of test repetitions
        b (int): constant term of the FV plaintext modulus (needed when scheme_type = 'FV')
    '''

    print("Computing the power function...");

    coefs = [0 for _ in range(power+1)];
    coefs[power] = 1.0;

    par = Params(scheme_type, params_index);
    par.set_ptxt_params(2*slots, b);
    scheme = Scheme(par);
    encdr = CyclIntEncoder(enc_delta, slots);
    scheme.set_encoder(encdr);

    q = scheme.min_q_for_poly_eval(coefs, bound);
    print("Minimal ciphertext modulus is ", q);
    if q == 0:
        raise ValueError("This parameter set does not support evaluation");
    par.set_mod(q);

    scheme.all_key_gen();

    max_approx_err = -1000.0;
    min_approx_err = 1000.0;

    for rnd in range(rounds):
        inp_vec = [float(bound*(-1)^(ZZ.random_element(2))) for _ in range(slots)];

        res = scheme.poly_eval_test(inp_vec, bound, coefs);
        if res == 0:
            print("Computation failed");

        res_ct = res[0];
        res_vec = res[1];
        res_vec_dec = res[2]; 

        approx_err = (vector([real(res_vec_dec[i]) for i in range(len(res_vec_dec))])-vector(res_vec)).norm(Infinity);
        print("Error between real approximation and encrypted values (log)", log(approx_err,2).n());

        approx_err = (vector([real(res_vec_dec[i]) for i in range(len(res_vec_dec))])-vector([(inp_vec[i])^power for i in range(len(inp_vec))])).norm(Infinity);
        max_approx_err = max(max_approx_err, log(approx_err,2).n());
        min_approx_err = min(min_approx_err, log(approx_err,2).n());
        if max_approx_err > -7:
            print("Small output precision. Increase parameters.");
            print("Input: ", inp_vec);
            break;

        print("Error between the power function and encrypted values (log)", log(approx_err,2).n());

        approx_err = (vector([real(res_vec[i]) for i in range(len(res_vec))])-vector([(inp_vec[i])^power for i in range(len(inp_vec))])).norm(Infinity);

        print("Error between the power function and its approximation (log)", log(approx_err,2).n());
        print("Round ", rnd, "has finished");
        print("Max. error so far:", max_approx_err);

    print("After ", rounds, " experiments the maximal approximation error is ", max_approx_err);
    print("and the minimal approximation is ", min_approx_err);


def exp_test(slots, bound, enc_delta, scheme_type, params_index, rounds, b=None):
    '''Computes an exponential function approximation and tests its correctness

    Parameters:
        slots (int): number of slots
        bound (int): bound on absolute values of data
        enc_delta (int): encoding scale
        scheme_type (str): scheme type
        params_index (int): parameter index
        rounds (int): number of test repetitions
        b (int): constant term of the FV plaintext modulus (needed when scheme_type = 'FV')
    '''

    print("Computing the power function...");

    coefs = [1.0, 1.0, 1.0/2.0, 1.0/6.0, 1.0/24.0, 1.0/120.0, 1.0/720.0, 1.0/5040.0, 1.0/40320.0];

    par = Params(scheme_type, params_index);
    par.set_ptxt_params(2*slots, b);
    scheme = Scheme(par);
    encdr = CyclIntEncoder(enc_delta, slots);
    scheme.set_encoder(encdr);

    q = scheme.min_q_for_poly_eval(coefs, bound);
    print("Minimal ciphertext modulus is ", q);
    if q == 0:
        raise ValueError("This parameter set does not support evaluation");
    par.set_mod(q);

    scheme.all_key_gen();

    max_approx_err = -1000.0;
    min_approx_err = 1000.0;

    for rnd in range(rounds):
        inp_vec = [float(bound*(-1)^(ZZ.random_element(2))) for _ in range(slots)];

        res = scheme.poly_eval_test(inp_vec, bound, coefs);
        if res == 0:
            print("Computation failed");

        res_ct = res[0];
        res_vec = res[1];
        res_vec_dec = res[2]; 

        approx_err = (vector([real(res_vec_dec[i]) for i in range(len(res_vec_dec))])-vector(res_vec)).norm(Infinity);
        print("Error between real approximation and encrypted values (log)", log(approx_err,2).n());

        approx_err = (vector([real(res_vec_dec[i]) for i in range(len(res_vec_dec))])-vector([exp(inp_vec[i]) for i in range(len(inp_vec))])).norm(Infinity);
        max_approx_err = max(max_approx_err, log(approx_err,2).n());
        min_approx_err = min(min_approx_err, log(approx_err,2).n());
        if max_approx_err > -7:
            print("Small output precision. Increase parameters.");
            print("Input: ", inp_vec);
            break;

        print("Error between the power function and encrypted values (log)", log(approx_err,2).n());

        approx_err = (vector([real(res_vec[i]) for i in range(len(res_vec))])-vector([exp(inp_vec[i]) for i in range(len(inp_vec))])).norm(Infinity);

        print("Error between the power function and its approximation (log)", log(approx_err,2).n());
        print("Round ", rnd, "has finished");
        print("Max. error so far:", max_approx_err);

    print("After ", rounds, " experiments the maximal approximation error is ", max_approx_err);
    print("and the minimal approximation is ", min_approx_err);

