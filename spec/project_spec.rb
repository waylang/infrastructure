require 'serverspec'

set :backend, :exec

describe file 'Vagrantfile' do
  it { should exist }
end

describe file 'version' do
  it { should exist }
  its(:content) { should match(/\d+\.\d+\.\d+/) }
end

describe file 'README.md' do
  it { should exist }
end

describe file 'Gemfile' do
  it { should exist }
end

describe file 'Berksfile' do
  it { should exist }
end

describe file 'Rakefile' do
  it { should exist }

  its(:content) do
    should include "Dir['vendor/infrastructure/tasks/**/*.rb']"\
      '.sort.each { |file| require_relative file }'
  end

  its(:content) do
    should include "Dir['tasks/**/*.rb'].sort.each { |file| require_relative file }"
  end
end

describe file 'metadata.rb' do
  it { should exist }

  its(:content) do
    should include "version File.read(Pathname.new(__FILE__).parent + 'version').strip"
  end
end

describe file 'chefignore' do
  it { should exist }
  its(:content) { should include 'vendor/*' }
end

describe file '.gitignore' do
  it { should exist }
  its(:content) { should include '.vagrant' }
  its(:content) { should include 'Gemfile.lock' }
  its(:content) { should include 'Berksfile.lock' }
end

describe file '.rubocop.yml' do
  it { should exist }
end

describe file '.editorconfig' do
  it { should exist }
end

describe file '.sublime-project' do
  it { should exist }
end

describe file 'recipes/vagrant.rb' do
  it { should exist }
end

describe file 'spec/vagrant_spec.rb' do
  it { should exist }
end

describe file 'spec/spec_helper.rb' do
  it { should exist }
end

describe file '.gitmodules' do
  its(:content) { should_not include 'git@github.com' }
end
