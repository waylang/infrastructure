require 'pathname'

name 'book'
version File.read(Pathname.new(__FILE__).parent + 'version').strip
depends 'infrastructure'
