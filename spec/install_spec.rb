require 'tmpdir'
require 'serverspec'

set :backend, :exec

directory = Dir.mktmpdir 'install-spec-'

describe command "cd #{directory} && TEST=true $OLDPWD/install 2>&1" do
  it('has output') { puts subject.stdout } if ENV['CI']
  its(:exit_status) { should eq 0 }
end

# It should stage all generated files
describe command "cd #{directory} && git diff --exit-code" do
  its(:exit_status) { should eq 0 }
end

describe command "rm -rf #{directory}" do
  its(:exit_status) { should eq 0 }
end
