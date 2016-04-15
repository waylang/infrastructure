require 'spec_helper'

describe 'metatheory::common' do
  let(:chef_run) { ChefSpec::SoloRunner.new.converge(described_recipe) }

  it 'includes infrastructure::common' do
    expect(chef_run).to include_recipe('infrastructure::common')
  end

  it 'installs coq' do
    expect(chef_run).to install_package('coq')
  end
end
