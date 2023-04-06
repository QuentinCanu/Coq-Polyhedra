#! /usr/bin/env python3

import json, os, math
import networkx as nx

with open(os.path.join(os.getcwd(), "data", "poly20dim21", f'poly20dim21.json')) as stream:
  contents = json.load(stream)

graph_lex = contents['graph_lex']
graph = nx.Graph({i : tuple(graph_lex[i]) for i in range(len(graph_lex))})
center = [2266, 2267, 2268, 2269, 2270, 2271, 2272, 2273, 2298, 2299, 2300, 2301, 2302, 2303, 2304, 2305, 2330, 2331, 2332, 2333, 2334, 2335, 2336, 2337, 2338, 2339, 2340, 2341, 2342, 2343, 2344, 2345, 2402, 2403, 2404, 2405, 2406, 2407, 2408, 2409, 2490, 2491, 2492, 2493, 2494, 2495, 2496, 2497, 2498, 2499, 2500, 2501, 2502, 2503, 2504, 2505, 2577, 2578, 2579, 2580, 2581, 2582, 2583, 2584, 2705, 2706, 2707, 2708, 2709, 2710, 2711, 2712, 2713, 2714, 2715, 2716, 2717, 2718, 2719, 2720, 2737, 2738, 2739, 2740, 2741, 2742, 2743, 2744, 2745, 2746, 2747, 2748, 2749, 2750, 2751, 2752, 2801, 2802, 2803, 2804, 2805, 2806, 2807, 2808, 2809, 2810, 2811, 2812, 2813, 2814, 2815, 2816, 2857, 2858, 2859, 2861, 2864, 2865, 2866, 2867, 2869, 2872, 2873, 2874, 2875, 2876, 2877, 2878, 2879, 2880, 2881, 2882, 2883, 2888, 2889, 2890, 2891, 2892, 2893, 2894, 2895, 2896, 2897, 2898, 2899, 2908, 2917, 2918, 2919, 2924, 2925, 2926, 2927, 2929, 2932, 2933, 2934, 2935, 2937, 2940, 2941, 2942, 2943, 2944, 2945, 2946, 2947, 2948, 2949, 2950, 2951, 2956, 2957, 2958, 2959, 2960, 2961, 2962, 2963, 2964, 2965, 2966, 2967, 2968, 2969, 2970, 2971, 2972, 2973, 2974, 2975, 2976, 2985, 2986, 2987, 2992, 2993, 2994, 2995, 2997, 3000, 3001, 3002, 3003, 3005, 3008, 3009, 3010, 3011, 3012, 3013, 3014, 3015, 3016, 3017, 3018, 3019, 3024, 3033, 3034, 3035, 3044, 3045, 3046, 3047, 3048, 3049, 3050, 3051, 3052, 3053, 3054, 3055, 3060, 3061, 3062, 3063, 3065, 3068, 3069, 3070, 3071, 3073, 3076, 3085, 3086, 3087, 3092, 3101, 3102, 3103, 3112, 3121, 3122, 3123, 3128, 3129, 3130, 3131, 3133, 3136, 3137, 3138, 3139, 3141, 3144, 3153, 3154, 3155, 3160, 3161, 3162, 3163, 3164, 3165, 3166, 3167, 3168, 3169, 3170, 3171, 3172, 3173, 3174, 3175, 3176, 3177, 3178, 3179, 3180, 3181, 3182, 3183, 3184, 3185, 3186, 3187, 3188, 3189, 3190, 3191, 3196, 3197, 3198, 3199, 3201, 3204, 3205, 3206, 3207, 3209, 3212, 3213, 3214, 3215, 3216, 3217, 3218, 3219, 3220, 3221, 3222, 3223, 3228, 3229, 3230, 3231, 3232, 3233, 3234, 3235, 3236, 3237, 3238, 3239, 3240, 3241, 3242, 3243, 3244, 3245, 3246, 3247, 3248, 3249, 3250, 3251, 3252, 3253, 3254, 3255, 3256, 3257, 3258, 3259, 3264, 3265, 3266, 3267, 3269, 3272, 3273, 3274, 3275, 3277, 3280, 3289, 3290, 3291, 3296, 3305, 3306, 3307, 3316, 3325, 3326, 3327, 3332, 3333, 3334, 3335, 3337, 3340, 3341, 3342, 3343, 3345, 3348, 3349, 3350, 3351, 3352, 3353, 3354, 3355, 3356, 3357, 3358, 3359, 3364, 3365, 3366, 3367, 3368, 3369, 3370, 3371, 3372, 3373, 3374, 3375, 3376, 3377, 3378, 3379, 3380, 3381, 3382, 3383, 3384, 3385, 3386, 3387, 3388, 3389, 3390, 3391, 3392, 3393, 3394, 3395, 3400, 3401, 3402, 3403, 3405, 3408, 3409, 3410, 3411, 3413, 3416, 3425, 3426, 3427, 3432, 3441, 3442, 3443, 3452, 3461, 3462, 3463, 3468, 5415, 5416, 5417, 5418, 5419, 5420, 5421, 5422, 5423, 5424, 5425, 5426, 5427, 5428, 5429, 5430, 5487, 5488, 5489, 5490, 5491, 5492, 5493, 5494, 5575, 5576, 5577, 5578, 5579, 5580, 5581, 5582, 5583, 5584, 5585, 5586, 5587, 5588, 5589, 5590, 5720, 5721, 5722, 5723, 5724, 5725, 5726, 5727, 5848, 5849, 5850, 5851, 5852, 5853, 5854, 5855, 5856, 5857, 5858, 5859, 5860, 5861, 5862, 5863, 5880, 5881, 5882, 5883, 5884, 5885, 5886, 5887, 5888, 5889, 5890, 5891, 5892, 5893, 5894, 5895, 6001, 6002, 6003, 6004, 6007, 6009, 6010, 6011, 6012, 6015, 6016, 6017, 6018, 6019, 6020, 6021, 6022, 6023, 6025, 6026, 6027, 6031, 6032, 6033, 6034, 6035, 6036, 6037, 6038, 6039, 6041, 6042, 6043, 6044, 6047, 6049, 6050, 6051, 6055, 6057, 6058, 6059, 6060, 6063, 6073, 6074, 6075, 6079, 6089, 6090, 6091, 6095, 6097, 6098, 6099, 6100, 6103, 6105, 6106, 6107, 6108, 6111, 6112, 6113, 6114, 6115, 6116, 6117, 6118, 6119, 6121, 6122, 6123, 6127, 6128, 6129, 6130, 6131, 6132, 6133, 6134, 6135, 6137, 6138, 6139, 6140, 6143, 6145, 6146, 6147, 6151, 6153, 6154, 6155, 6156, 6159, 6160, 6161, 6162, 6163, 6164, 6165, 6166, 6167, 6169, 6170, 6171, 6175, 6185, 6186, 6187, 6191, 6193, 6194, 6195, 6196, 6199, 6201, 6202, 6203, 6204, 6207, 6208, 6209, 6210, 6211, 6212, 6213, 6214, 6215, 6217, 6218, 6219, 6223, 6233, 6234, 6235, 6236, 6239, 6241, 6242, 6243, 6247, 6249, 6250, 6251, 6252, 6255, 6265, 6266, 6267, 6271, 6272, 6273, 6274, 6275, 6276, 6277, 6278, 6279, 6281, 6282, 6283, 6287, 6289, 6290, 6291, 6292, 6295, 6297, 6298, 6299, 6300, 6303, 6313, 6314, 6315, 6319, 6329, 6330, 6331, 6332, 6335, 6337, 6338, 6339, 6343, 6345, 6346, 6347, 6348, 6351, 6361, 6362, 6363, 6367, 6377, 6378, 6379, 6383, 6385, 6386, 6387, 6388, 6391, 6393, 6394, 6395, 6396, 6399, 6409, 6410, 6411, 6415, 6416, 6417, 6418, 6419, 6420, 6421, 6422, 6423, 6425, 6426, 6427, 6428, 6431, 6433, 6434, 6435, 6439, 6441, 6442, 6443, 6444, 6447, 6448, 6449, 6450, 6451, 6452, 6453, 6454, 6455, 6457, 6458, 6459, 6463, 6464, 6465, 6466, 6467, 6468, 6469, 6470, 6471, 6473, 6474, 6475, 6479, 6481, 6482, 6483, 6484, 6487, 6489, 6490, 6491, 6492, 6495, 6496, 6497, 6498, 6499, 6500, 6501, 6502, 6503, 6505, 6506, 6507, 6511, 6512, 6513, 6514, 6515, 6516, 6517, 6518, 6519, 6521, 6522, 6523, 6524, 6527, 6529, 6530, 6531, 6535, 6537, 6538, 6539, 6540, 6543, 6544, 6545, 6546, 6547, 6548, 6549, 6550, 6551, 6553, 6554, 6555, 6559, 6560, 6561, 6562, 6563, 6564, 6565, 6566, 6567, 6569, 6570, 6571, 6575, 6577, 6578, 6579, 6580, 6583, 6585, 6586, 6587, 6588, 6591, 6601, 6602, 6603, 6607, 6617, 6618, 6619, 6620, 6623, 6625, 6626, 6627, 6631, 6633, 6634, 6635, 6636, 6639, 6649, 6650, 6651, 6655, 6665, 6666, 6667, 6671, 6673, 6674, 6675, 6676, 6679, 6681, 6682, 6683, 6684, 6687, 6688, 6689, 6690, 6691, 6692, 6693, 6694, 6695, 6697, 6698, 6699, 6703, 6713, 6714, 6715, 6716, 6719, 6721, 6722, 6723, 6727, 6729, 6730, 6731, 6732, 6735, 6745, 6746, 6747, 6751, 6752, 6753, 6754, 6755, 6756, 6757, 6758, 6759, 6761, 6762, 6763, 6767, 6769, 6770, 6771, 6772, 6775, 6777, 6778, 6779, 6780, 6783, 6793, 6794, 6795, 6799, 6809, 6810, 6811, 6812, 6815, 6817, 6818, 6819, 6823, 6825, 6826, 6827, 6828, 6831, 6841, 6842, 6843, 6847, 6857, 6858, 6859, 6863, 8650, 8651, 8652, 8653, 8654, 8655, 8656, 8657, 8658, 8659, 8660, 8661, 8662, 8663, 8664, 8665, 8682, 8683, 8684, 8685, 8686, 8687, 8688, 8689, 8690, 8691, 8692, 8693, 8694, 8695, 8696, 8697, 8714, 8715, 8716, 8717, 8718, 8719, 8720, 8721, 8786, 8787, 8788, 8789, 8790, 8791, 8792, 8793, 8810, 8811, 8812, 8813, 8814, 8815, 8816, 8817, 8818, 8819, 8820, 8821, 8822, 8823, 8824, 8825, 8874, 8875, 8876, 8877, 8878, 8879, 8880, 8881, 8882, 8883, 8884, 8885, 8886, 8887, 8888, 8889, 8961, 8962, 8963, 8964, 8965, 8966, 8967, 8968, 8969, 8970, 8971, 8972, 8973, 8974, 8975, 8976, 8977, 8978, 8979, 8980, 8981, 8982, 8983, 8984, 8993, 8994, 8995, 8997, 9000, 9001, 9002, 9005, 9008, 9009, 9010, 9011, 9013, 9016, 9017, 9018, 9020, 9021, 9022, 9024, 9027, 9028, 9029, 9030, 9031, 9033, 9036, 9037, 9038, 9041, 9044, 9045, 9046, 9047, 9048, 9049, 9050, 9051, 9052, 9061, 9062, 9063, 9065, 9068, 9069, 9070, 9073, 9076, 9077, 9078, 9079, 9081, 9084, 9085, 9086, 9087, 9088, 9089, 9090, 9092, 9095, 9096, 9097, 9098, 9099, 9101, 9104, 9105, 9106, 9109, 9112, 9113, 9114, 9115, 9116, 9117, 9118, 9119, 9120, 9121, 9122, 9123, 9124, 9125, 9126, 9127, 9128, 9129, 9130, 9131, 9133, 9136, 9137, 9138, 9141, 9144, 9145, 9146, 9147, 9149, 9152, 9154, 9156, 9157, 9158, 9160, 9163, 9164, 9165, 9166, 9167, 9169, 9172, 9173, 9174, 9177, 9180, 9197, 9198, 9199, 9201, 9204, 9205, 9206, 9209, 9212, 9213, 9214, 9215, 9217, 9220, 9222, 9224, 9225, 9226, 9228, 9231, 9232, 9233, 9234, 9235, 9237, 9240, 9241, 9242, 9245, 9248, 9257, 9258, 9259, 9260, 9261, 9262, 9263, 9264, 9265, 9266, 9267, 9269, 9272, 9273, 9274, 9277, 9280, 9281, 9282, 9283, 9285, 9288, 9289, 9290, 9291, 9292, 9293, 9294, 9296, 9299, 9300, 9301, 9302, 9303, 9305, 9308, 9309, 9310, 9313, 9316, 9317, 9318, 9319, 9320, 9321, 9322, 9323, 9324, 9325, 9326, 9327, 9328, 9329, 9330, 9331, 9332, 9333, 9334, 9335, 9337, 9340, 9341, 9342, 9345, 9348, 9349, 9350, 9351, 9353, 9356, 9357, 9358, 9359, 9360, 9361, 9362, 9364, 9367, 9368, 9369, 9370, 9371, 9373, 9376, 9377, 9378, 9381, 9384, 9401, 9402, 9403, 9405, 9408, 9409, 9410, 9413, 9416, 9417, 9418, 9419, 9421, 9424, 9426, 9428, 9429, 9430, 9432, 9435, 9436, 9437, 9438, 9439, 9441, 9444, 9445, 9446, 9449, 9452, 9453, 9454, 9455, 9456, 9457, 9458, 9459, 9460, 9461, 9462, 9463, 9464, 9465, 9466, 9467, 9468, 9469, 9470, 9471, 9473, 9476, 9477, 9478, 9481, 9484, 9485, 9486, 9487, 9489, 9492, 9493, 9494, 9495, 9496, 9497, 9498, 9500, 9503, 9504, 9505, 9506, 9507, 9509, 9512, 9513, 9514, 9517, 9520, 9537, 9538, 9539, 9541, 9544, 9545, 9546, 9549, 9552, 9553, 9554, 9555, 9557, 9560, 9562, 9564, 9565, 9566, 9568, 9571, 9572, 9573, 9574, 9575, 9577, 9580, 9581, 9582, 9585, 9588, 11028, 11029, 11030, 11031, 11032, 11033, 11034, 11035, 11036, 11037, 11038, 11039, 11040, 11041, 11042, 11043, 11044, 11045, 11046, 11047, 11048, 11049, 11050, 11051, 11068, 11069, 11070, 11071, 11072, 11073, 11074, 11075, 11076, 11077, 11078, 11079, 11080, 11081, 11082, 11083, 11084, 11085, 11086, 11087, 11088, 11089, 11090, 11091, 11108, 11109, 11110, 11111, 11112, 11113, 11114, 11115, 11116, 11117, 11118, 11119, 11120, 11121, 11122, 11123, 11204, 11205, 11206, 11207, 11208, 11209, 11210, 11211, 11228, 11229, 11230, 11231, 11232, 11233, 11234, 11235, 11236, 11237, 11238, 11239, 11240, 11241, 11242, 11243, 11244, 11245, 11246, 11247, 11248, 11249, 11250, 11251, 11308, 11309, 11310, 11311, 11312, 11313, 11314, 11315, 11316, 11317, 11318, 11319, 11320, 11321, 11322, 11323, 11324, 11325, 11326, 11327, 11328, 11329, 11330, 11331, 11411, 11412, 11413, 11414, 11415, 11416, 11417, 11418, 11419, 11420, 11421, 11422, 11423, 11424, 11425, 11426, 11435, 11437, 11438, 11439, 11442, 11443, 11445, 11446, 11447, 11450, 11451, 11452, 11454, 11456, 11457, 11458, 11461, 11462, 11463, 11465, 11466, 11467, 11470, 11479, 11481, 11482, 11483, 11486, 11487, 11489, 11490, 11491, 11494, 11495, 11496, 11497, 11498, 11500, 11501, 11502, 11505, 11506, 11507, 11509, 11510, 11511, 11514, 11515, 11516, 11517, 11518, 11519, 11520, 11521, 11522, 11523, 11525, 11526, 11527, 11530, 11531, 11533, 11534, 11535, 11538, 11540, 11542, 11544, 11545, 11546, 11549, 11550, 11551, 11553, 11554, 11555, 11558, 11567, 11569, 11570, 11571, 11574, 11575, 11577, 11578, 11579, 11582, 11584, 11586, 11588, 11589, 11590, 11593, 11594, 11595, 11597, 11598, 11599, 11602, 11603, 11604, 11605, 11606, 11607, 11608, 11609, 11610, 11611, 11613, 11614, 11615, 11618, 11619, 11621, 11622, 11623, 11626, 11627, 11628, 11629, 11630, 11632, 11633, 11634, 11637, 11638, 11639, 11641, 11642, 11643, 11646, 11647, 11648, 11649, 11650, 11651, 11652, 11653, 11654, 11655, 11657, 11658, 11659, 11662, 11663, 11665, 11666, 11667, 11670, 11671, 11672, 11673, 11674, 11676, 11677, 11678, 11681, 11682, 11683, 11685, 11686, 11687, 11690, 11699, 11701, 11702, 11703, 11706, 11707, 11709, 11710, 11711, 11714, 11716, 11718, 11720, 11721, 11722, 11725, 11726, 11727, 11729, 11730, 11731, 11734, 11735, 11736, 11737, 11738, 11739, 11740, 11741, 11742, 11743, 11745, 11746, 11747, 11750, 11751, 11753, 11754, 11755, 11758, 11759, 11760, 11761, 11762, 11764, 11765, 11766, 11769, 11770, 11771, 11773, 11774, 11775, 11778, 11787, 11789, 11790, 11791, 11794, 11795, 11797, 11798, 11799, 11802, 11804, 11806, 11808, 11809, 11810, 11813, 11814, 11815, 11817, 11818, 11819, 11822, 12967, 12968, 12969, 12970, 12971, 12972, 12973, 12974, 12975, 12976, 12977, 12978, 12979, 12980, 12981, 12982, 13039, 13040, 13041, 13042, 13043, 13044, 13045, 13046, 13127, 13128, 13129, 13130, 13131, 13132, 13133, 13134, 13135, 13136, 13137, 13138, 13139, 13140, 13141, 13142, 13214, 13215, 13216, 13217, 13218, 13219, 13220, 13221, 13342, 13343, 13344, 13345, 13346, 13347, 13348, 13349, 13350, 13351, 13352, 13353, 13354, 13355, 13356, 13357, 13374, 13375, 13376, 13377, 13378, 13379, 13380, 13381, 13382, 13383, 13384, 13385, 13386, 13387, 13388, 13389, 13438, 13439, 13440, 13441, 13442, 13443, 13444, 13445, 13446, 13447, 13448, 13449, 13450, 13451, 13452, 13453, 13494, 13496, 13497, 13498, 13501, 13502, 13504, 13505, 13506, 13509, 13510, 13511, 13512, 13513, 13514, 13515, 13516, 13517, 13518, 13519, 13520, 13521, 13522, 13523, 13524, 13525, 13526, 13527, 13528, 13537, 13546, 13548, 13549, 13550, 13553, 13554, 13556, 13557, 13558, 13561, 13562, 13563, 13564, 13565, 13566, 13567, 13568, 13569, 13570, 13571, 13572, 13573, 13574, 13575, 13576, 13577, 13578, 13579, 13580, 13581, 13582, 13583, 13584, 13585, 13586, 13587, 13588, 13589, 13598, 13600, 13601, 13602, 13605, 13606, 13608, 13609, 13610, 13613, 13614, 13615, 13616, 13617, 13618, 13619, 13620, 13621, 13630, 13631, 13632, 13641, 13642, 13643, 13644, 13645, 13646, 13647, 13648, 13649, 13650, 13652, 13653, 13654, 13657, 13658, 13660, 13661, 13662, 13665, 13682, 13683, 13684, 13693, 13702, 13704, 13705, 13706, 13709, 13710, 13712, 13713, 13714, 13717, 13726, 13727, 13728, 13729, 13730, 13731, 13732, 13733, 13734, 13735, 13736, 13737, 13738, 13739, 13740, 13741, 13742, 13743, 13744, 13745, 13746, 13747, 13748, 13749, 13750, 13751, 13752, 13753, 13754, 13756, 13757, 13758, 13761, 13762, 13764, 13765, 13766, 13769, 13770, 13771, 13772, 13773, 13774, 13775, 13776, 13777, 13778, 13779, 13780, 13781, 13782, 13783, 13784, 13785, 13786, 13787, 13788, 13789, 13790, 13791, 13792, 13793, 13794, 13795, 13796, 13797, 13798, 13799, 13800, 13801, 13802, 13803, 13804, 13805, 13806, 13808, 13809, 13810, 13813, 13814, 13816, 13817, 13818, 13821, 13838, 13839, 13840, 13849, 13858, 13860, 13861, 13862, 13865, 13866, 13868, 13869, 13870, 13873, 13874, 13875, 13876, 13877, 13878, 13879, 13880, 13881, 13882, 13883, 13884, 13885, 13886, 13887, 13888, 13889, 13890, 13891, 13892, 13893, 13894, 13895, 13896, 13897, 13898, 13899, 13900, 13901, 13902, 13903, 13904, 13905, 13906, 13907, 13908, 13909, 13910, 13912, 13913, 13914, 13917, 13918, 13920, 13921, 13922, 13925, 13942, 13943, 13944, 13953, 14242, 14243, 14244, 14245, 14246, 14247, 14248, 14249, 14250, 14251, 14252, 14253, 14254, 14255, 14256, 14257, 14258, 14259, 14260, 14261, 14262, 14263, 14264, 14265, 14298, 14299, 14300, 14301, 14302, 14303, 14304, 14305, 14630, 14631, 14632, 14633, 14634, 14635, 14636, 14637, 14638, 14639, 14640, 14641, 14642, 14643, 14644, 14645, 14702, 14703, 14704, 14705, 14706, 14707, 14708, 14709, 14790, 14791, 14792, 14793, 14794, 14795, 14796, 14797, 14798, 14799, 14800, 14801, 14802, 14803, 14804, 14805, 14935, 14936, 14937, 14938, 14939, 14940, 14941, 14942, 15063, 15064, 15065, 15066, 15067, 15068, 15069, 15070, 15071, 15072, 15073, 15074, 15075, 15076, 15077, 15078, 15095, 15096, 15097, 15098, 15099, 15100, 15101, 15102, 15103, 15104, 15105, 15106, 15107, 15108, 15109, 15110, 15216, 15217, 15218, 15219, 15222, 15224, 15225, 15226, 15227, 15230, 15231, 15232, 15233, 15234, 15235, 15236, 15237, 15238, 15240, 15241, 15242, 15243, 15247, 15248, 15249, 15250, 15251, 15252, 15253, 15254, 15256, 15257, 15258, 15259, 15262, 15264, 15265, 15266, 15267, 15272, 15273, 15274, 15275, 15278, 15288, 15289, 15290, 15291, 15304, 15305, 15306, 15307, 15312, 15313, 15314, 15315, 15318, 15320, 15321, 15322, 15323, 15326, 15327, 15328, 15329, 15330, 15331, 15332, 15333, 15334, 15336, 15337, 15338, 15339, 15343, 15344, 15345, 15346, 15347, 15348, 15349, 15350, 15352, 15353, 15354, 15355, 15358, 15360, 15361, 15362, 15363, 15368, 15369, 15370, 15371, 15374, 15375, 15376, 15377, 15378, 15379, 15380, 15381, 15382, 15384, 15385, 15386, 15387, 15400, 15401, 15402, 15403, 15408, 15409, 15410, 15411, 15414, 15416, 15417, 15418, 15419, 15422, 15423, 15424, 15425, 15426, 15427, 15428, 15429, 15430, 15432, 15433, 15434, 15435, 15448, 15449, 15450, 15451, 15454, 15456, 15457, 15458, 15459, 15464, 15465, 15466, 15467, 15470, 15480, 15481, 15482, 15483, 15487, 15488, 15489, 15490, 15491, 15492, 15493, 15494, 15496, 15497, 15498, 15499, 15504, 15505, 15506, 15507, 15510, 15512, 15513, 15514, 15515, 15518, 15528, 15529, 15530, 15531, 15544, 15545, 15546, 15547, 15550, 15552, 15553, 15554, 15555, 15560, 15561, 15562, 15563, 15566, 15576, 15577, 15578, 15579, 15592, 15593, 15594, 15595, 15600, 15601, 15602, 15603, 15606, 15608, 15609, 15610, 15611, 15614, 15624, 15625, 15626, 15627, 15631, 15632, 15633, 15634, 15635, 15636, 15637, 15638, 15640, 15641, 15642, 15643, 15646, 15648, 15649, 15650, 15651, 15656, 15657, 15658, 15659, 15662, 15663, 15664, 15665, 15666, 15667, 15668, 15669, 15670, 15672, 15673, 15674, 15675, 15679, 15680, 15681, 15682, 15683, 15684, 15685, 15686, 15688, 15689, 15690, 15691, 15696, 15697, 15698, 15699, 15702, 15704, 15705, 15706, 15707, 15710, 15711, 15712, 15713, 15714, 15715, 15716, 15717, 15718, 15720, 15721, 15722, 15723, 15727, 15728, 15729, 15730, 15731, 15732, 15733, 15734, 15736, 15737, 15738, 15739, 15742, 15744, 15745, 15746, 15747, 15752, 15753, 15754, 15755, 15758, 15759, 15760, 15761, 15762, 15763, 15764, 15765, 15766, 15768, 15769, 15770, 15771, 15775, 15776, 15777, 15778, 15779, 15780, 15781, 15782, 15784, 15785, 15786, 15787, 15792, 15793, 15794, 15795, 15798, 15800, 15801, 15802, 15803, 15806, 15816, 15817, 15818, 15819, 15832, 15833, 15834, 15835, 15838, 15840, 15841, 15842, 15843, 15848, 15849, 15850, 15851, 15854, 15864, 15865, 15866, 15867, 15880, 15881, 15882, 15883, 15888, 15889, 15890, 15891, 15894, 15896, 15897, 15898, 15899, 15902, 15903, 15904, 15905, 15906, 15907, 15908, 15909, 15910, 15912, 15913, 15914, 15915, 15928, 15929, 15930, 15931, 15934, 15936, 15937, 15938, 15939, 15944, 15945, 15946, 15947, 15950, 15960, 15961, 15962, 15963, 15967, 15968, 15969, 15970, 15971, 15972, 15973, 15974, 15976, 15977, 15978, 15979, 15984, 15985, 15986, 15987, 15990, 15992, 15993, 15994, 15995, 15998, 16008, 16009, 16010, 16011, 16024, 16025, 16026, 16027, 16030, 16032, 16033, 16034, 16035, 16040, 16041, 16042, 16043, 16046, 16056, 16057, 16058, 16059, 16072, 16073, 16074, 16075, 16718, 16719, 16720, 16721, 16722, 16723, 16724, 16725, 16726, 16727, 16728, 16729, 16730, 16731, 16732, 16733, 16750, 16751, 16752, 16753, 16754, 16755, 16756, 16757, 16758, 16759, 16760, 16761, 16762, 16763, 16764, 16765, 16782, 16783, 16784, 16785, 16786, 16787, 16788, 16789, 16854, 16855, 16856, 16857, 16858, 16859, 16860, 16861, 16878, 16879, 16880, 16881, 16882, 16883, 16884, 16885, 16886, 16887, 16888, 16889, 16890, 16891, 16892, 16893, 16942, 16943, 16944, 16945, 16946, 16947, 16948, 16949, 17046, 17047, 17048, 17049, 17050, 17051, 17052, 17053, 17086, 17087, 17088, 17089, 17090, 17091, 17092, 17093, 17142, 17143, 17144, 17145, 17146, 17147, 17148, 17149, 17150, 17151, 17152, 17153, 17154, 17155, 17156, 17157, 17174, 17175, 17176, 17177, 17178, 17179, 17180, 17181, 17182, 17183, 17184, 17185, 17186, 17187, 17188, 17189, 17246, 17247, 17248, 17249, 17250, 17251, 17252, 17253, 17286, 17287, 17288, 17289, 17290, 17291, 17292, 17293, 17303, 17304, 17305, 17306, 17309, 17311, 17313, 17314, 17317, 17319, 17320, 17321, 17322, 17325, 17326, 17327, 17328, 17329, 17330, 17331, 17332, 17333, 17335, 17337, 17338, 17341, 17351, 17352, 17353, 17354, 17357, 17359, 17361, 17362, 17365, 17367, 17368, 17369, 17370, 17373, 17375, 17377, 17378, 17381, 17382, 17383, 17384, 17385, 17386, 17387, 17388, 17389, 17399, 17400, 17401, 17402, 17405, 17407, 17409, 17410, 17413, 17415, 17416, 17417, 17418, 17421, 17422, 17423, 17424, 17425, 17426, 17427, 17428, 17429, 17431, 17433, 17434, 17437, 17438, 17439, 17440, 17441, 17442, 17443, 17444, 17445, 17447, 17448, 17449, 17450, 17453, 17455, 17457, 17458, 17461, 17463, 17464, 17465, 17466, 17469, 17471, 17473, 17474, 17477, 17478, 17479, 17480, 17481, 17482, 17483, 17484, 17485, 17486, 17487, 17488, 17489, 17490, 17491, 17492, 17493, 17495, 17496, 17497, 17498, 17501, 17503, 17505, 17506, 17509, 17511, 17512, 17513, 17514, 17517, 17527, 17529, 17530, 17533, 17543, 17544, 17545, 17546, 17549, 17551, 17553, 17554, 17557, 17559, 17560, 17561, 17562, 17565, 17567, 17569, 17570, 17573, 17591, 17592, 17593, 17594, 17597, 17599, 17601, 17602, 17605, 17607, 17608, 17609, 17610, 17613, 17623, 17625, 17626, 17629, 17639, 17640, 17641, 17642, 17645, 17647, 17649, 17650, 17653, 17655, 17656, 17657, 17658, 17661, 17663, 17665, 17666, 17669, 17678, 17679, 17680, 17681, 17682, 17683, 17684, 17685, 17687, 17688, 17689, 17690, 17693, 17695, 17697, 17698, 17701, 17703, 17704, 17705, 17706, 17709, 17710, 17711, 17712, 17713, 17714, 17715, 17716, 17717, 17719, 17721, 17722, 17725, 17726, 17727, 17728, 17729, 17730, 17731, 17732, 17733, 17735, 17736, 17737, 17738, 17741, 17743, 17745, 17746, 17749, 17751, 17752, 17753, 17754, 17757, 17759, 17761, 17762, 17765, 17766, 17767, 17768, 17769, 17770, 17771, 17772, 17773, 17774, 17775, 17776, 17777, 17778, 17779, 17780, 17781, 17783, 17784, 17785, 17786, 17789, 17791, 17793, 17794, 17797, 17799, 17800, 17801, 17802, 17805, 17806, 17807, 17808, 17809, 17810, 17811, 17812, 17813, 17815, 17817, 17818, 17821, 17822, 17823, 17824, 17825, 17826, 17827, 17828, 17829, 17831, 17832, 17833, 17834, 17837, 17839, 17841, 17842, 17845, 17847, 17848, 17849, 17850, 17853, 17855, 17857, 17858, 17861, 17879, 17880, 17881, 17882, 17885, 17887, 17889, 17890, 17893, 17895, 17896, 17897, 17898, 17901, 17911, 17913, 17914, 17917, 17927, 17928, 17929, 17930, 17933, 17935, 17937, 17938, 17941, 17943, 17944, 17945, 17946, 17949, 17951, 17953, 17954, 17957, 17958, 17959, 17960, 17961, 17962, 17963, 17964, 17965, 17966, 17967, 17968, 17969, 17970, 17971, 17972, 17973, 17975, 17976, 17977, 17978, 17981, 17983, 17985, 17986, 17989, 17991, 17992, 17993, 17994, 17997, 18007, 18009, 18010, 18013, 18023, 18024, 18025, 18026, 18029, 18031, 18033, 18034, 18037, 18039, 18040, 18041, 18042, 18045, 18047, 18049, 18050, 18053, 18071, 18072, 18073, 18074, 18077, 18079, 18081, 18082, 18085, 18087, 18088, 18089, 18090, 18093, 18103, 18105, 18106, 18109, 18119, 18120, 18121, 18122, 18125, 18127, 18129, 18130, 18133, 18135, 18136, 18137, 18138, 18141, 18143, 18145, 18146, 18149, 18819, 18820, 18821, 18822, 18823, 18824, 18825, 18826, 18827, 18828, 18829, 18830, 18831, 18832, 18833, 18834, 18851, 18852, 18853, 18854, 18855, 18856, 18857, 18858, 18859, 18860, 18861, 18862, 18863, 18864, 18865, 18866, 18883, 18884, 18885, 18886, 18887, 18888, 18889, 18890, 18955, 18956, 18957, 18958, 18959, 18960, 18961, 18962, 18979, 18980, 18981, 18982, 18983, 18984, 18985, 18986, 18987, 18988, 18989, 18990, 18991, 18992, 18993, 18994, 19043, 19044, 19045, 19046, 19047, 19048, 19049, 19050, 19147, 19148, 19149, 19150, 19151, 19152, 19153, 19154, 19187, 19188, 19189, 19190, 19191, 19192, 19193, 19194, 19243, 19244, 19245, 19246, 19247, 19248, 19249, 19250, 19251, 19252, 19253, 19254, 19255, 19256, 19257, 19258, 19275, 19276, 19277, 19278, 19279, 19280, 19281, 19282, 19283, 19284, 19285, 19286, 19287, 19288, 19289, 19290, 19347, 19348, 19349, 19350, 19351, 19352, 19353, 19354, 19387, 19388, 19389, 19390, 19391, 19392, 19393, 19394, 19404, 19405, 19406, 19407, 19410, 19412, 19414, 19415, 19420, 19421, 19422, 19423, 19426, 19427, 19428, 19429, 19430, 19431, 19432, 19433, 19434, 19436, 19438, 19439, 19452, 19453, 19454, 19455, 19458, 19460, 19462, 19463, 19468, 19469, 19470, 19471, 19474, 19476, 19478, 19479, 19483, 19484, 19485, 19486, 19487, 19488, 19489, 19490, 19500, 19501, 19502, 19503, 19506, 19508, 19510, 19511, 19516, 19517, 19518, 19519, 19522, 19523, 19524, 19525, 19526, 19527, 19528, 19529, 19530, 19532, 19534, 19535, 19539, 19540, 19541, 19542, 19543, 19544, 19545, 19546, 19548, 19549, 19550, 19551, 19554, 19556, 19558, 19559, 19564, 19565, 19566, 19567, 19570, 19572, 19574, 19575, 19579, 19580, 19581, 19582, 19583, 19584, 19585, 19586, 19587, 19588, 19589, 19590, 19591, 19592, 19593, 19594, 19596, 19597, 19598, 19599, 19602, 19604, 19606, 19607, 19612, 19613, 19614, 19615, 19618, 19628, 19630, 19631, 19644, 19645, 19646, 19647, 19650, 19652, 19654, 19655, 19660, 19661, 19662, 19663, 19666, 19668, 19670, 19671, 19692, 19693, 19694, 19695, 19698, 19700, 19702, 19703, 19708, 19709, 19710, 19711, 19714, 19724, 19726, 19727, 19740, 19741, 19742, 19743, 19746, 19748, 19750, 19751, 19756, 19757, 19758, 19759, 19762, 19764, 19766, 19767, 19779, 19780, 19781, 19782, 19783, 19784, 19785, 19786, 19788, 19789, 19790, 19791, 19794, 19796, 19798, 19799, 19804, 19805, 19806, 19807, 19810, 19811, 19812, 19813, 19814, 19815, 19816, 19817, 19818, 19820, 19822, 19823, 19827, 19828, 19829, 19830, 19831, 19832, 19833, 19834, 19836, 19837, 19838, 19839, 19842, 19844, 19846, 19847, 19852, 19853, 19854, 19855, 19858, 19860, 19862, 19863, 19867, 19868, 19869, 19870, 19871, 19872, 19873, 19874, 19875, 19876, 19877, 19878, 19879, 19880, 19881, 19882, 19884, 19885, 19886, 19887, 19890, 19892, 19894, 19895, 19900, 19901, 19902, 19903, 19906, 19907, 19908, 19909, 19910, 19911, 19912, 19913, 19914, 19916, 19918, 19919, 19923, 19924, 19925, 19926, 19927, 19928, 19929, 19930, 19932, 19933, 19934, 19935, 19938, 19940, 19942, 19943, 19948, 19949, 19950, 19951, 19954, 19956, 19958, 19959, 19980, 19981, 19982, 19983, 19986, 19988, 19990, 19991, 19996, 19997, 19998, 19999, 20002, 20012, 20014, 20015, 20028, 20029, 20030, 20031, 20034, 20036, 20038, 20039, 20044, 20045, 20046, 20047, 20050, 20052, 20054, 20055, 20059, 20060, 20061, 20062, 20063, 20064, 20065, 20066, 20067, 20068, 20069, 20070, 20071, 20072, 20073, 20074, 20076, 20077, 20078, 20079, 20082, 20084, 20086, 20087, 20092, 20093, 20094, 20095, 20098, 20108, 20110, 20111, 20124, 20125, 20126, 20127, 20130, 20132, 20134, 20135, 20140, 20141, 20142, 20143, 20146, 20148, 20150, 20151, 20172, 20173, 20174, 20175, 20178, 20180, 20182, 20183, 20188, 20189, 20190, 20191, 20194, 20204, 20206, 20207, 20220, 20221, 20222, 20223, 20226, 20228, 20230, 20231, 20236, 20237, 20238, 20239, 20242, 20244, 20246, 20247]

barycenter = [21917]

pred = contents["pred"]
leaves = [1 for _ in pred]
for v,_,_ in pred:
  leaves[v] = 0
print(sum(leaves))


# pred = contents["pred"]
# pred_vect = contents["pred_vect"]
# bases = contents["bases"]

# lengths = [math.inf for _ in pred]
# lengths[0] = 0
# for i in range(1,len(pred)):
#     idx = i
#     count = 0
#     while idx != 0:
#         idx = pred[idx][0]
#         count += 1
#     lengths[i] = count
# print("max length = ", max(lengths))

# mean = 0
# count = 0
# maxn = -math.inf
# for idx,mat in enumerate(pred_vect):
#   base = bases[idx]
#   for col in mat:
#     for i in range(len(col)):
#         if i not in base:
#           l = len(col[i])
#           mean += l
#           count += 1
#           if l > maxn:
#             maxn = l
# print("mean = ", mean/count, "; max = ", maxn)