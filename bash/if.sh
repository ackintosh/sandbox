# https://qiita.com/wakayama-y/items/a9b7380263da77e51711

# #############################################################################
# 数値
# #############################################################################

# equal
test_num=10
if [ ${test_num} -eq 10 ];then
	echo num_equal
fi

# not equal
test_num=1
if [ ${test_num} -ne 10 ];then
	echo num_not_equal
fi

# less than
test_num=1
if [ ${test_num} -lt 10 ];then
	echo num_less_than
fi

# less than or equal
test_num=10
if [ ${test_num} -le 10 ];then
	echo num_less_than_or_equal
fi

# greater than
test_num=10
if [ ${test_num} -gt 1 ];then
	echo num_greater_than
fi

# greater than or equal
test_num=10
if [ ${test_num} -ge 10 ];then
	echo num_greater_than_or_equal
fi


# #############################################################################
# 文字列
# #############################################################################

test_str=aaa
if [ "${test_str}" = "aaa" ];then
	echo str_equal
fi

test_str=aaa
if [ "${test_str}" != "bbb" ];then
	echo str_not_equal
fi


# #############################################################################
# ファイル・ディレクトリ
# #############################################################################

# -d
# ディレクトリならtrue
if [ -d ../lighthouse ];then
	echo "-d"
fi

if [ -d ../README.md ];then
	echo "READMEはファイルなのでfalse"
fi

# -f
# 普通のファイルならtrue
if [ -f ../README.md ];then
	echo "-f"
fi

if [ -f ../lighthouse ];then
	echo "lighthouseはディレクトリなのでfalse"
fi

# -s
# サイズが 0 より大きければtrue
if [ -s ../README.md ];then
	echo "-s"
fi

if [ -s ./emptyfile ];then
	echo "サイズが 0 なのでfalse"
fi

if [ -s ./emptyfileeeeee ];then
	echo "存在しないファイルなのでfalse"
fi

# -e
# 存在するならtrue
if [ -e ./emptyfile ];then
	echo "-e"
fi

if [ -s ./emptyfileeeeee ];then
	echo "存在しないファイルなのでfalse"
fi


