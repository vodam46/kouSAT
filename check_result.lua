local function parse(file)
	local line = file:read('*l')
	while line:sub(1,1) ~= 'p' do line = file:read('*l') end
	line = line:sub(7)
	local f = string.gmatch(line, '%w+')
	local vars = tonumber(f())
	local clauses = tonumber(f())

	local cnf = {}
	local clause = {}
	while #cnf < clauses do
		local n = file:read('*n')
		if n == 0 then
			table.insert(cnf, clause)
			clause = {}
		else
			table.insert(clause, n)
		end
	end
	file:close()
	return cnf, vars
end

local cnf, vars = parse(io.open(arg[1], "r"))

local result = io.stdin:read('*l')
local values = {}
local func = string.gmatch(result, "[^ ]+")
while true do
	local s = func()
	if s ~= 'v' then
		local n = tonumber(s)
		if n == nil then
			print(s)
			print("error")
			break
		end
		if n == 0 then break end
		values[math.abs(n)] = n>0
	end
end

assert(#values == vars)

for i, clause in ipairs(cnf) do
	local sat = false
	for _, var in ipairs(clause) do
		if values[math.abs(var)] == (var>0) then
			sat = true
			break
		end
	end
	if not sat then
		print(arg[1])
		print("clause is not true", i)
		print(require'inspect'(clause))
	end
end
